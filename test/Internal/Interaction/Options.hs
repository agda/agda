{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Options ( tests ) where

import Agda.Interaction.Library (getPrimitiveLibDir)
import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Utils.Monad
import Agda.Syntax.Parser

import Data.List (intercalate)
import qualified Data.Set as Set

import System.FilePath ((</>), takeExtension)

import Utils (getAgdaFilesInDir, SearchMode(Rec))

import Internal.Helpers hiding (reason)

prop_defaultOptions :: Bool
prop_defaultOptions =
  case runOptM (checkOpts defaultOptions) of
    (Right _, []) -> True
    _ -> False

-- | The default pragma options should be considered safe.

prop_defaultPragmaOptionsSafe :: Property
prop_defaultPragmaOptionsSafe = ioProperty $
  case runOptM $ safeFlag defaultPragmaOptions of
    (Right opts, []) ->
      case unsafePragmaOptions opts of
        []         -> yes
        unsafe     -> no $ "Following pragmas are default but not safe: " ++ intercalate ", " unsafe
    (Right _ , ws) -> no $ "Unexpected warning(s): " ++ show ws
    (Left errs, _) -> no $ "Unexpected error: " ++ errs
  where
  yes :: IO Bool
  yes = return True
  no :: String -> IO Bool
  no msg = False <$ putStrLn msg


prop_allBuiltinsSafePostulatesOrNot :: Property
prop_allBuiltinsSafePostulatesOrNot = ioProperty helper
  where
    helper :: IO Bool
    helper = do
      libdirPrim <- getPrimitiveLibDir
      allFiles <- getAgdaFilesInDir Rec libdirPrim
      let builtinFiles = Set.map (libdirPrim </>) builtinModules
      let diff = Set.difference (Set.fromList allFiles) builtinFiles
      if null diff then return True else do
        putStrLn $ "Missing/spurious builtins: " ++ show diff
        return False

prop_BuiltinsSafeIntersectUnsafe :: Property
prop_BuiltinsSafeIntersectUnsafe = ioProperty helper
  where
    helper :: IO Bool
    helper = do
      let intersect = Set.intersection builtinModulesWithSafePostulates builtinModulesWithUnsafePostulates
      if null intersect then return True else do
        putStrLn $ "Builtins both allowed and not allowed postulates: " ++ show intersect
        return False

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Interaction.Options" $allProperties
