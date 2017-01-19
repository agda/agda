{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

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
import Agda.Utils.Functor
import Agda.Utils.IndexedList

import Agda.Compiler.ToTreeless
import Agda.Compiler.Common
import Agda.Main (runAgdaWithOptions, optionError, runTCMPrettyErrors, defaultInteraction)

#include "undefined.h"

-- Public interface -------------------------------------------------------

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

data Recompile menv mod = Recompile menv | Skip mod

runAgda :: [Backend] -> IO ()
runAgda backends = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  opts     <- liftIO $ runOptM $ parseOptions backends argv
  case opts of
    Left  err              -> liftIO $ optionError err
    Right (backends, opts) -> () <$ runAgdaWithOptions generateHTML (interaction backends) progName opts

-- Internals --------------------------------------------------------------

data BackendWithOpts opts where
  BackendWithOpts :: Backend' opts env menv mod def -> BackendWithOpts opts

backendWithOpts :: Backend -> Some BackendWithOpts
backendWithOpts (Backend backend) = Some (BackendWithOpts backend)

forgetOpts :: BackendWithOpts opts -> Backend
forgetOpts (BackendWithOpts backend) = Backend backend

bOptions :: Lens' opts (BackendWithOpts opts)
bOptions f (BackendWithOpts b) = f (options b) <&> \ opts -> BackendWithOpts b{ options = opts }

embedFlag :: Lens' a b -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' a b -> OptDescr (Flag a) -> OptDescr (Flag b)
embedOpt l = fmap (embedFlag l)

parseOptions :: [Backend] -> [String] -> OptM ([Backend], CommandLineOptions)
parseOptions backends argv =
  case makeAll backendWithOpts backends of
    Some bs -> do
      let agdaFlags    = map (embedOpt lSnd) standardOptions
          backendFlags = do
            Some i            <- forgetAll Some $ allIndices bs
            BackendWithOpts b <- [lookupIndex bs i]
            opt               <- commandLineFlags b
            return $ embedOpt (lFst . lIndex i . bOptions) opt
      (backends, opts) <- getOptSimple argv (agdaFlags ++ backendFlags) (embedFlag lSnd . inputFlag)
                                            (bs, defaultOptions)
      opts <- checkOpts opts
      let enabled (Backend b) = isEnabled b (options b)
      return (filter enabled $ forgetAll forgetOpts backends, opts)

interaction :: [Backend] -> TCM (Maybe Interface) -> TCM ()
interaction [] check = do
  opts <- commandLineOptions
  defaultInteraction opts check
interaction backends check = do
  mi     <- check
  noMain <- optCompileNoMain <$> commandLineOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain
  case mi of
    Nothing -> __IMPOSSIBLE__
    Just i  -> sequence_ [ compilerMain backend isMain i | Backend backend <- backends ]

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

