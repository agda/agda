{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Print modules imported by an agda file by only parsing the file.

module Main where

------------------------------------------------------------------------------
-- Haskell base imports

import Prelude        ( IO, String, pattern Right, (.), ($), putStrLn, unwords )
import Data.Foldable  ( mapM_ )
import Data.Functor   ( (<$>) )
import Data.Monoid    ( mempty )
import Data.Semigroup ( (<>) )
import Data.Set       ( Set )
import Data.Text.Lazy ( unpack )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common.Pretty    ( prettyShow )
import Agda.Syntax.Concrete         ( Declaration(Import), modDecls )
import Agda.Syntax.Concrete.Generic ( foldDecl )
import Agda.Syntax.Parser           ( moduleParser, parseFile, readFilePM, runPMIO )
import Agda.Syntax.Position         ( mkRangeFile )

import Agda.Utils.FileName          ( absolute )
import Agda.Utils.Null              ( empty )
import Agda.Utils.Singleton         ( singleton )

-- | Print the modules a (fixed) agda file imports.
--
main :: IO ()
main = do

  -- Create an absolute path as the parser API wants it.

  let file  = "../../std-lib/src/Data/List/Relation/Unary/Any.agda"
  afile <- absolute file
  let rfile = mkRangeFile afile empty

  -- Call the module parser, ignoring errors and warnings.

  (Right ((modul, _), _), _) <- runPMIO $ do
    txt <- unpack <$> readFilePM rfile
    parseFile moduleParser rfile txt

  -- Print all imports in the parsed module.

  putStrLn $ unwords [ file, "imports the following modules:" ]
  mapM_ (putStrLn . ("- " <>)) $ allImports $ modDecls modul

-- | Get the names of all modules that are imported
--   somewhere (deep) inside the given declarations.
--
allImports :: [Declaration] -> Set String
allImports = foldDecl \case
  Import _ x _ _ _ -> singleton $ prettyShow x
  _ -> mempty
