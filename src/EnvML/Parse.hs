
module EnvML.Parse
  ( parseEmlFile
  , parseEmliFile
  , compileEmlFile
  , module EnvML.Syntax
  ) where

import EnvML.Syntax
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)
import qualified EnvML.Desugar as Desugar
import qualified EnvML.Desugared as D
import System.FilePath (takeDirectory, (</>))

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path

-- | Collect top-level import names from a parsed module.
collectImports :: Module -> [Name]
collectImports (Struct structs) = [n | Import n <- structs]
collectImports _                = []

-- | Parse an .eml file, resolve each import by reading the corresponding
-- .emli file in the same directory, and desugar with import types.
-- The result is a nested functor: one parameter per import (left-to-right = outermost first).
compileEmlFile :: FilePath -> IO D.Module
compileEmlFile path = do
  m <- parseEmlFile path
  let baseDir     = takeDirectory path
      importNames = collectImports m
  importTypes <- mapM (\n -> fmap (\mty -> (n, mty)) (parseEmliFile (baseDir </> n ++ ".emli"))) importNames
  return $ Desugar.desugarModuleWithImports importTypes m
