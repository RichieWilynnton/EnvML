module EnvML.Build (build) where

import Control.Monad (foldM)
import Control.Exception (evaluate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.FilePath (takeDirectory, takeBaseName, (</>))
import System.Directory (doesFileExist)

import qualified EnvML.Parse as Parse
import qualified CoreFE.Syntax as CoreFE

data ObjFile = ObjFile
  { objDeps :: [String]
  , objExp  :: CoreFE.Exp
  } deriving (Show, Read)

data Visit = Unvisited | InProgress | Done

-- Returns modules in dependency order (leaves first).
topoSort :: Map.Map String [String] -> Either String [String]
topoSort graph = do
  (_, order) <- foldM visit (Map.fromList [(n, Unvisited) | n <- Map.keys graph], []) (Map.keys graph)
  return order
  where
    visit (states, order) node =
      case Map.findWithDefault Done node states of
        Done       -> Right (states, order)
        InProgress -> Left $ "Cyclic dependency involving: " ++ node
        Unvisited  -> dfs (Map.insert node InProgress states) order node

    dfs states order node = do
      let deps = Map.findWithDefault [] node graph
      (states', order') <- foldM visit (states, order) deps
      return (Map.insert node Done states', order' ++ [node])

-- | Transitively discover all modules reachable from an entry file by
-- following imports in both .eml and .emli files.
-- All files are assumed to be in the same directory.
discoverDeps :: FilePath -> String -> IO (Map.Map String [String])
discoverDeps dir = go Map.empty . Set.singleton
  where
    go acc queue
      | Set.null queue = return acc
      | otherwise = do
          let (name, rest) = Set.deleteFindMin queue
          if Map.member name acc
            then go acc rest
            else do
              let emlPath  = dir </> name ++ ".eml"
                  emliPath = dir </> name ++ ".emli"
              emlExists <- doesFileExist emlPath
              if not emlExists
                then error $ "Module '" ++ name ++ "' not found: " ++ emlPath
                else do
                  srcMod <- Parse.parseEmlFile emlPath
                  let emlDeps = Parse.collectEmlImports srcMod
                  emliExists <- doesFileExist emliPath
                  emliDeps <- if emliExists
                    then do
                      mty <- Parse.parseEmliFile emliPath
                      return (Parse.collectEmliImports mty)
                    else return []
                  let allDeps = Set.toList $ Set.fromList (emlDeps ++ emliDeps)
                  go (Map.insert name allDeps acc) (rest `Set.union` Set.fromList allDeps)

-- | Build a project starting from a single .eml entry file.
-- Transitively discovers all imported modules, topologically sorts them,
-- and compiles + links each in order.
build :: (FilePath -> IO ()) -> (String -> IO ()) -> FilePath -> IO ()
build compile link entryPath = do
  let dir  = takeDirectory entryPath
      name = takeBaseName entryPath

  depMap <- discoverDeps dir name

  case topoSort depMap of
    Left err -> putStrLn $ "Build failed: " ++ err
    Right order -> do
      putStrLn $ "=== Build: " ++ entryPath ++ " ==="
      putStrLn $ "  Build order: " ++ unwords order
      mapM_ (buildOne dir compile link) order
      putStrLn "\n=== Build complete ==="

buildOne :: FilePath -> (FilePath -> IO ()) -> (String -> IO ()) -> String -> IO ()
buildOne dir compile link name = do
  let emlPath  = dir </> name ++ ".eml"
      emloPath = dir </> name ++ ".emlo"
  putStrLn $ "\n--- [" ++ name ++ "] Compiling ---"
  compile emlPath
  exists <- doesFileExist emloPath
  if exists
    then do
      contents <- readFile emloPath
      obj <- evaluate (read contents :: ObjFile)
      let depEmles = map (\d -> dir </> d ++ ".emle") (objDeps obj)
          linkArgs = unwords (emloPath : depEmles)
      putStrLn $ "--- [" ++ name ++ "] Linking ---"
      link linkArgs
    else
      putStrLn $ "\x2717 Skipping link for " ++ name ++ " (compilation failed)"
