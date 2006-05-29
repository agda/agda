{-# OPTIONS -cpp -fglasgow-exts#-}

module Interacton.GhciTop where

import Prelude hiding (print, putStr, putStrLn)
import System.IO hiding (print, putStr, putStrLn)
import System.IO.Unsafe
import Data.IORef

import Utils.Fresh
import Utils.Monad
import Utils.Monad.Undo
import Utils.IO

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Exception
import Data.List as List
import Data.Map as Map
import System.Exit

import TypeChecker
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Reduce

import Syntax.Position
import Syntax.Parser
import Syntax.Concrete.Pretty ()
import Syntax.Abstract
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Abstract.Test
import Syntax.Abstract.Name

import Interaction.Exceptions
import qualified Interaction.BasicOps as BO

theTCState :: IORef(TCState)
theTCState   = unsafePerformIO $ newIORef(initState)

theTCEnv   :: IORef(TCEnv)
theTCEnv   = unsafePerformIO $ newIORef(initEnv)

theUndoStack :: IORef([TCState])
theUndoStack = unsafePerformIO $ newIORef([])

ioTCM :: TCM a -> IO a
ioTCM cmd = do 
  us  <- readIORef theUndoStack
  st  <- readIORef theTCState
  env <- readIORef theTCEnv
  (runTCM $ putUndoStack us >> put st >>
            liftM3 (,,) (local (const env) cmd) get getUndoStack)
    >>= either (\ err         -> print err >> exitWith(ExitFailure 1))
               (\ (a,st',ss') -> writeIORef theTCState st' >>
                                 writeIORef theUndoStack ss' >> return a)
cmd_load :: String -> IO ()
cmd_load file = crashOnException $ do
    (m',scope) <- concreteToAbstract_ =<< parseFile moduleParser file
    ioTCM $ setUndo >> resetState >> checkDecl m' >> setScope scope
      
cmd_constraints :: IO ()
cmd_constraints = crashOnException $ do
    putStrLn . unlines . List.map prc . Map.assocs =<< ioTCM getConstraints
  where prc (x,(_,ctx,c)) = show x ++ ": " ++ show ctx ++ " |- " ++ show c

cmd_metas :: IO ()
cmd_metas = crashOnException $ ioTCM BO.getMetas >>= putStrLn . unlines

cmd_undo :: IO ()
cmd_undo = ioTCM $ undo

cmd_give :: InteractionId -> String -> IO(String,[InteractionId])
cmd_give ii s = crashOnException $ ioTCM $ do
    (e, iis) <- BO.give ii Nothing =<< parseExprIn ii s
    return (show e, iis)

parseExprIn :: InteractionId -> String -> TCM(Expr)
parseExprIn ii s = do
    mi <- getMetaInfo <$> (lookupMeta =<< lookupInteractionId ii)
    i  <- fresh
    liftIO $ concreteToAbstract
             (ScopeState {freshId = i})
             (metaScope mi)
             (parsePosString exprParser (rStart (metaRange mi)) s)

