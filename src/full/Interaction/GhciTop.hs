{-# OPTIONS -cpp -fglasgow-exts#-}

module Interaction.GhciTop where

import Prelude hiding (print, putStr, putStrLn)
import System.IO hiding (print, putStr, putStrLn)
import System.IO.Unsafe
import Data.IORef

import Utils.Fresh
import Utils.Monad
import Utils.Monad.Undo
import Utils.IO
import Utils.Pretty

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
import qualified Syntax.Concrete as SC
import Syntax.Concrete.Pretty ()
import Syntax.Abstract
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Abstract.Test
import Syntax.Abstract.Name

import Interaction.Exceptions
import qualified Interaction.BasicOps as B
import qualified Interaction.CommandLine.CommandLine as CL

theTCState :: IORef TCState
theTCState = unsafePerformIO $ newIORef initState

theTCEnv :: IORef TCEnv
theTCEnv = unsafePerformIO $ newIORef initEnv

theUndoStack :: IORef [TCState]
theUndoStack = unsafePerformIO $ newIORef []

ioTCM :: TCM a -> IO a
ioTCM cmd = do 
  us  <- readIORef theUndoStack
  st  <- readIORef theTCState
  env <- readIORef theTCEnv
  res <- runTCM $ do
    putUndoStack us
    put st
    x <- withEnv env cmd
    st <- get
    us <- getUndoStack
    return (x,st,us)
  case res of
    Left err -> do
	print err
	exitWith $ ExitFailure 1
    Right (a,st',ss') -> do
	writeIORef theTCState st'
	writeIORef theUndoStack ss'
        putStrLn $ "debug: stack depth = " ++ show (length ss')
	return a

cmd_load :: String -> IO ()
cmd_load file = crashOnException $ do
    (m',scope) <- concreteToAbstract_ =<< parseFile moduleParser file
    is <- ioTCM $ do setUndo; resetState; checkDecl m'; setScope scope; lispIP
    putStrLn $ response $ L[A"agda2-load-action", is]
  where lispIP  = format . sortRng <$> (tagRng =<< getInteractionPoints)
        tagRng  = mapM (\i -> (,)i <$> getInteractionRange i)
        sortRng = sortBy ((.snd) . compare . snd)
        format  = Q . L . List.map (A . tail . show . fst)
                  
cmd_constraints :: IO ()
cmd_constraints = crashOnException $
    ioTCM B.getConstraints >>= mapM_ (putStrLn . show . abstractToConcrete_)

cmd_metas :: IO ()
cmd_metas = crashOnException $ ioTCM $ CL.showMetas []

cmd_undo :: IO ()
cmd_undo = ioTCM undo

cmd_give :: InteractionId -> Range -> String -> IO()
cmd_give = give_gen B.give $ \s ce -> case ce of (SC.Paren _ _)-> "'paren"
                                                 _             -> "'no-paren"

cmd_refine :: InteractionId -> Range -> String -> IO ()
cmd_refine = give_gen B.refine $ \s -> show . show

give_gen give_ref mk_newtxt ii rng s = crashOnException $ ioTCM $ do
    prec      <- contextPrecedence <$> getInteractionScope ii
    (ae, iis) <- give_ref ii Nothing =<< parseExprIn ii rng s
    let newtxt = A . mk_newtxt s $ abstractToConcreteCtx prec ae
        newgs  = Q . L $ List.map showNumIId iis
    liftIO $ putStrLn $ response $
           L[A"agda2-give-action", showNumIId ii, newtxt, newgs]


parseExprIn :: InteractionId -> Range -> String -> TCM(Expr)
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaRange mId rng       
    mi  <- getMetaInfo <$> lookupMeta mId
    i   <- fresh
    liftIO $ concreteToAbstract
             (ScopeState {freshId = i})
             (metaScope mi)
             (parsePosString exprParser (rStart (metaRange mi)) s)

response :: Lisp String -> String
response l = show (text "agda2_mode_code" <+> pretty l)

data Lisp a = A a | L [Lisp a] | Q (Lisp a)

instance Pretty a => Pretty (Lisp a) where
  pretty (A a ) = pretty a
  pretty (L xs) = parens (sep (List.map pretty xs))
  pretty (Q x)  = text "'"<>pretty x

instance Pretty String where pretty = text

instance Pretty a => Show (Lisp a) where show = show . pretty

showNumIId = A . tail . show
quoteString s = '"':concatMap q s++"\"" where
  q '\n' = "\\n"
  q ch   = [ch]
  
