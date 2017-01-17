{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( Backend(..), Backend'(..), Recompile(..), IsMain(..)
  , Flag
  , runAgda
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad )
  where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import System.Environment
import System.Exit
import System.Console.GetOpt

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Interaction.Highlighting.HTML

import Agda.Utils.Pretty
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Impossible

import Agda.Compiler.ToTreeless
import Agda.Compiler.Common
import Agda.Main (runAgdaWithOptions, optionError, runTCMPrettyErrors, defaultInteraction)

#include "undefined.h"

data Recompile menv mod = Recompile menv | Skip mod

data Backend where
  Backend :: Backend' opts env menv mod def -> Backend

data Backend' opts env menv mod def = Backend'
  { backendName      :: String
  , options          :: opts
  , commandLineFlags :: [OptDescr (Flag opts)]
  , isEnabled        :: opts -> Bool
  , preCompile       :: opts -> TCM env
  , postCompile      :: env -> IsMain -> Map ModuleName mod -> TCM ()
  , preModule        :: env -> ModuleName -> FilePath -> TCM (Recompile menv mod)
  , compileDef       :: env -> menv -> Definition -> TCM def
  , postModule       :: env -> menv -> ModuleName -> [def] -> TCM mod
  }

_1 :: Lens' a (a, b)
_1 f (x, y) = (, y) <$> f x

_2 :: Lens' b (a, b)
_2 f (x, y) = (x,) <$> f y

embedFlag :: Lens' a b -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' a b -> OptDescr (Flag a) -> OptDescr (Flag b)
embedOpt l = fmap (embedFlag l)

parseOptions :: Backend' opts env menv mod def -> [String] -> OptM (opts, CommandLineOptions)
parseOptions backend argv = do
  let agdaFlags    = map (embedOpt _2) standardOptions
      backendFlags = map (embedOpt _1) (commandLineFlags backend)
  (bopts, opts) <- getOptSimple argv (agdaFlags ++ backendFlags) (embedFlag _2 . inputFlag)
                                (options backend, defaultOptions)
  opts <- checkOpts opts
  return (bopts, opts)

runAgda :: Backend -> IO ()
runAgda (Backend backend) = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  opts     <- liftIO $ runOptM $ parseOptions backend argv
  case opts of
    Left  err  -> liftIO $ optionError err
    Right (bopts, opts) -> () <$ runAgdaWithOptions generateHTML interaction progName opts
      where
        interaction | isEnabled backend bopts = backendInteraction backend{ options = bopts }
                    | otherwise               = defaultInteraction opts

backendInteraction :: Backend' opts env menv mod def -> TCM (Maybe Interface) -> TCM ()
backendInteraction backend check = do
  mi <- check
  noMain <- optCompileNoMain <$> commandLineOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain
  case mi of
    Nothing -> __IMPOSSIBLE__
    Just i  -> compilerMain backend isMain i

compilerMain :: Backend' opts env menv mod def -> IsMain -> Interface -> TCM ()
compilerMain backend isMain i =
  inCompilerEnv i $ do
    env  <- preCompile backend (options backend)
    mods <- doCompile isMain i $ \ isMain i -> Map.singleton (iModuleName i) <$> compileModule backend env i
    postCompile backend env isMain mods

compileModule :: Backend' opts env menv mod def -> env -> Interface -> TCM mod
compileModule backend env i = do
  ifile <- maybe __IMPOSSIBLE__ filePath <$>
            (findInterfaceFile . toTopLevelModuleName =<< curMName)
  r <- preModule backend env (iModuleName i) ifile
  case r of
    Skip m         -> return m
    Recompile menv -> do
      defs  <- map snd . sortDefs <$> curDefs
      postModule backend env menv (iModuleName i) =<< mapM (compileDef backend env menv) defs

