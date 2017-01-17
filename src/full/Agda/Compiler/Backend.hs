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

data All :: (x -> *) -> [x] -> * where
  Nil  :: All p '[]
  Cons :: p x -> All p xs -> All p (x : xs)

data Elem :: x -> [x] -> * where
  Zero :: Elem x (x : xs)
  Suc  :: Elem x xs -> Elem x (y : xs)

ix :: Elem x xs -> Lens' (p x) (All p xs)
ix Zero    f (Cons x xs) = f x       <&> \ x  -> Cons x xs
ix (Suc i) f (Cons x xs) = ix i f xs <&> \ xs -> Cons x xs

data BackendWithOpts opts where
  BackendWithOpts :: Backend' opts env menv mod def -> BackendWithOpts opts

backendWithOpts :: Backend -> Some BackendWithOpts
backendWithOpts (Backend backend) = Some (BackendWithOpts backend)

forgetOpts :: BackendWithOpts opts -> Backend
forgetOpts (BackendWithOpts backend) = Backend backend

bOptions :: Lens' opts (BackendWithOpts opts)
bOptions f (BackendWithOpts b) = f (options b) <&> \ opts -> BackendWithOpts b{ options = opts }

data Some :: (k -> *) -> * where
  Some :: f i -> Some f

makeAll :: (a -> Some b) -> [a] -> Some (All b)
makeAll f [] = Some Nil
makeAll f (x : xs) =
  case (f x, makeAll f xs) of
    (Some y, Some ys) -> Some (Cons y ys)

data ElemAll :: (x -> *) -> [x] -> * where
  ElemAll :: Elem x xs -> p x -> ElemAll p xs

sucElemAll :: ElemAll p xs -> ElemAll p (x : xs)
sucElemAll (ElemAll i x) = ElemAll (Suc i) x

allElems :: All p xs -> [ElemAll p xs]
allElems Nil = []
allElems (Cons x xs) = ElemAll Zero x : map sucElemAll (allElems xs)

embedFlag :: Lens' a b -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' a b -> OptDescr (Flag a) -> OptDescr (Flag b)
embedOpt l = fmap (embedFlag l)

forgetAll :: (forall x. b x -> a) -> All b xs -> [a]
forgetAll f Nil         = []
forgetAll f (Cons x xs) = f x : forgetAll f xs

parseOptions :: [Backend] -> [String] -> OptM ([Backend], CommandLineOptions)
parseOptions backends argv =
  case makeAll backendWithOpts backends of
    Some bs -> do
      let agdaFlags    = map (embedOpt _2) standardOptions
          backendFlags = do
            ElemAll i (BackendWithOpts backend) <- allElems bs
            opt <- commandLineFlags backend
            return $ embedOpt (_1 . ix i . bOptions) opt
      (backends, opts) <- getOptSimple argv (agdaFlags ++ backendFlags) (embedFlag _2 . inputFlag)
                                            (bs, defaultOptions)
      opts <- checkOpts opts
      let enabled (Backend b) = isEnabled b (options b)
      return (filter enabled $ forgetAll forgetOpts backends, opts)

runAgda :: [Backend] -> IO ()
runAgda backends = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  opts     <- liftIO $ runOptM $ parseOptions backends argv
  case opts of
    Left  err              -> liftIO $ optionError err
    Right (backends, opts) -> () <$ runAgdaWithOptions generateHTML (interaction backends) progName opts

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

