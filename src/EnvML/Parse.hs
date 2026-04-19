
module EnvML.Parse
  ( parseEmlFile
  , parseEmliFile
  , collectEmlImports
  , collectEmliImports
  , module EnvML.Syntax
  ) where

import EnvML.Syntax
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path

-- | Collect top-level import names from a parsed module.
collectEmlImports :: Module -> [Name]
collectEmlImports (Struct structs) = [n | Import n <- structs]
collectEmlImports _                = []

-- | Collect import names from a parsed interface.
collectEmliImports :: ModuleTyp -> [Name]
collectEmliImports (TySig intf) = [n | ImportDecl n <- intf]
collectEmliImports _            = []