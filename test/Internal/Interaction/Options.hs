{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Options ( tests ) where

import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Utils.Monad
import Agda.Syntax.Parser

import Data.List
import qualified Data.Set as Set

import System.FilePath ((</>), takeExtension)

import Utils (getAgdaFilesInDir, SearchMode(Rec))

import Internal.Helpers

prop_defaultOptions :: Property
prop_defaultOptions = ioProperty $
  either (const False) (const True) <$> runOptM (checkOpts defaultOptions)

-- | The default pragma options should be considered safe.

prop_defaultPragmaOptionsSafe :: Property
prop_defaultPragmaOptionsSafe = ioProperty helper
  where
    helper :: IO Bool
    helper = do
      defaultSafe <- runOptM $ safeFlag defaultPragmaOptions
      case defaultSafe of
        Left errs -> do
          putStrLn $ "Unexpected error: " ++ errs
          return False
        Right opts -> let unsafe = unsafePragmaOptions opts in
          if null unsafe then return True else do
            putStrLn $ "Following pragmas are default but not safe: "
                                          ++ intercalate ", " unsafe
            return False

prop_allBuiltinsSafePostulatesOrNot :: Property
prop_allBuiltinsSafePostulatesOrNot = ioProperty helper
  where
    helper :: IO Bool
    helper = do
      libdirPrim <- (</> "prim") <$> defaultLibDir
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
