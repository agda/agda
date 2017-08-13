{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( Backend(..), Backend'(..), Recompile(..), IsMain(..)
  , Flag
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad
    -- For Agda.Main
  , backendInteraction
  , parseBackendOptions
    -- For InteractionTop
  , callBackend
  ) where

import Control.Monad.State

import qualified Data.List as List
import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map

import System.Environment
import System.Exit
import System.Console.GetOpt

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty as P

import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Interaction.Highlighting.HTML
import Agda.Interaction.Imports (getAllWarnings')

import Agda.Utils.Pretty
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Impossible
import Agda.Utils.Functor
import Agda.Utils.IndexedList

import Agda.Compiler.ToTreeless
import Agda.Compiler.Common

#include "undefined.h"

-- Public interface -------------------------------------------------------

data Backend where
  Backend :: Backend' opts env menv mod def -> Backend

data Backend' opts env menv mod def = Backend'
  { backendName      :: String
  , backendVersion   :: Maybe String
      -- ^ Optional version information to be printed with @--version@.
  , options          :: opts
      -- ^ Default options
  , commandLineFlags :: [OptDescr (Flag opts)]
      -- ^ Backend-specific command-line flags. Should at minimum contain a
      --   flag to enable the backend.
  , isEnabled        :: opts -> Bool
      -- ^ Unless the backend has been enabled, @runAgda@ will fall back to
      --   vanilla Agda behaviour.
  , preCompile       :: opts -> TCM env
      -- ^ Called after type checking completes, but before compilation starts.
  , postCompile      :: env -> IsMain -> Map ModuleName mod -> TCM ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.
  , preModule        :: env -> ModuleName -> FilePath -> TCM (Recompile menv mod)
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required.
  , postModule       :: env -> menv -> IsMain -> ModuleName -> [def] -> TCM mod
      -- ^ Called after all definitions of a module has been compiled.
  , compileDef       :: env -> menv -> Definition -> TCM def
      -- ^ Compile a single definition.
  , scopeCheckingSuffices :: Bool
    -- ^ True if the backend works if @--only-scope-checking@ is used.
  }

data Recompile menv mod = Recompile menv | Skip mod

callBackend :: String -> IsMain -> Interface -> TCM ()
callBackend name iMain i = do
  backends <- use stBackends
  case [ b | b@(Backend b') <- backends, backendName b' == name ] of
    Backend b : _ -> compilerMain b iMain i
    []            -> genericError $ "No backend called '" ++ name ++ "' " ++
                                    "(installed backends: " ++
                                    List.intercalate ", " [ backendName b | Backend b <- backends ] ++ ")"

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

parseBackendOptions :: [Backend] -> [String] -> OptM ([Backend], CommandLineOptions)
parseBackendOptions backends argv =
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
      return (forgetAll forgetOpts backends, opts)

backendInteraction :: [Backend] -> (TCM (Maybe Interface) -> TCM ()) -> TCM (Maybe Interface) -> TCM ()
backendInteraction [] fallback check = fallback check
backendInteraction backends _ check = do
  opts   <- commandLineOptions
  let backendNames = [ backendName b | Backend b <- backends ]
      err flag = genericError $ "Cannot mix --" ++ flag ++ " and backends (" ++ List.intercalate ", " backendNames ++ ")"
  when (optInteractive     opts) $ err "interactive"
  when (optGHCiInteraction opts) $ err "interaction"
  mi     <- check

  -- reset warnings
  stTCWarnings .= []

  noMain <- optCompileNoMain <$> commandLineOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain
  case mi of
    Nothing -> genericError $ "You can only compile modules without unsolved metavariables."
    Just i  -> sequence_ [ compilerMain backend isMain i | Backend backend <- backends ]

  -- print warnings that might have accumulated during compilation
  ws <- filter (not . isUnsolvedWarning . tcWarning) <$> getAllWarnings' AllWarnings RespectFlags
  unless (null ws) $ reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> ws


compilerMain :: Backend' opts env menv mod def -> IsMain -> Interface -> TCM ()
compilerMain backend isMain i =
  inCompilerEnv i $ do
    onlyScoping <- optOnlyScopeChecking <$> commandLineOptions
    when (not (scopeCheckingSuffices backend) && onlyScoping) $
      genericError $
        "The --only-scope-checking flag cannot be combined with " ++
        backendName backend ++ "."
    env  <- preCompile backend (options backend)
    mods <- doCompile isMain i $ \ isMain i -> Map.singleton (iModuleName i) <$> compileModule backend env isMain i
    setInterface i
    postCompile backend env isMain mods

compileModule :: Backend' opts env menv mod def -> env -> IsMain -> Interface -> TCM mod
compileModule backend env isMain i = do
  ifile <- maybe __IMPOSSIBLE__ filePath <$>
            (findInterfaceFile . toTopLevelModuleName =<< curMName)
  r <- preModule backend env (iModuleName i) ifile
  case r of
    Skip m         -> return m
    Recompile menv -> do
      defs <- map snd . sortDefs <$> curDefs
      res  <- mapM (compileDef' backend env menv <=< instantiateFull) defs
      postModule backend env menv isMain (iModuleName i) res

compileDef' :: Backend' opts env menv mod def -> env -> menv -> Definition -> TCM def
compileDef' backend env menv def = setCurrentRange (defName def) $ compileDef backend env menv def
