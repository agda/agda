{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.GhciTop where

import Prelude hiding (print, putStr, putStrLn)
import System.IO hiding (print, putStr, putStrLn)
import System.IO.Unsafe
import Data.Char
import Data.IORef
import qualified Text.PrettyPrint as P

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
import TypeChecking.Monad as TM
import TypeChecking.Monad.Name as TMN
import TypeChecking.MetaVars
import TypeChecking.Reduce

import Syntax.Position
import Syntax.Parser
import qualified Syntax.Concrete as SC
import Syntax.Common as SCo
import Syntax.Concrete.Pretty ()
import Syntax.Abstract as SA
import Syntax.Internal as SI
import Syntax.Scope
import qualified Syntax.Info as Info
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Test
import Syntax.Abstract.Name

import Interaction.Exceptions
import qualified Interaction.BasicOps as B
import qualified Interaction.CommandLine.CommandLine as CL

#include "../undefined.h"

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

type GoalCommand = InteractionId -> Range -> String -> IO()

cmd_give :: GoalCommand
cmd_give = give_gen B.give $ \s ce -> case ce of (SC.Paren _ _)-> "'paren"
                                                 _             -> "'no-paren"

cmd_refine :: GoalCommand
cmd_refine = give_gen B.refine $ \s -> show . show

give_gen give_ref mk_newtxt ii rng s = crashOnException $ ioTCM $ do
    prec      <- contextPrecedence <$> getInteractionScope ii
    (ae, iis) <- give_ref ii Nothing =<< parseExprIn ii rng s
    let newtxt = A . mk_newtxt s $ abstractToConcreteCtx prec ae
        newgs  = Q . L $ List.map showNumIId iis
    liftIO $ putStrLn $ response $
           L[A"agda2-give-action", showNumIId ii, newtxt, newgs]

parseExprIn :: InteractionId -> Range -> String -> TCM Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaRange mId rng       
    mi  <- getMetaInfo <$> lookupMeta mId
    i   <- fresh
    liftIO $ concreteToAbstract
             (ScopeState {freshId = i})
             (metaScope mi)
             (parsePosString exprParser (rStart (metaRange mi)) s)

cmd_context :: GoalCommand
cmd_context ii _ _ = putStrLn . unlines . List.map show
                   =<< ioTCM (B.contextOfMeta ii)

cmd_infer :: B.Rewrite -> GoalCommand
cmd_infer norm ii rng s = crashOnException $ ioTCM $ do
    liftIO . putStrLn . show =<< B.typeInMeta ii norm =<< parseExprIn ii rng s


cmd_goal_type :: B.Rewrite -> GoalCommand
cmd_goal_type norm ii _ _ = crashOnException $ ioTCM $ do
    liftIO . putStrLn . show =<< B.typeOfMeta norm ii




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

quoteString s = '"':concatMap q s++"\"" where q '\n' = "\\n"
                                              q ch   = [ch]

cmd_make_case :: GoalCommand
cmd_make_case ii rng s = crashOnException $ ioTCM $ do
  mId <- lookupInteractionId ii
  mfo <- getMetaInfo <$> lookupMeta mId
  ex  <- parseExprIn ii rng s
  passAVar ex -- the pattern variable to case on
  let sx = show ex
  -- find the clause to refine
  -- (dnam, oldpas) <- findClause mId =<< getSignature -- not the metaSig.
  targetPat <- findClause mId =<< getSignature -- not the metaSig.
  withMetaInfo mfo $ do
    -- gather constructors for ex
    (vx,tx) <- inferExpr ex
    El(SI.Def d _) _ <- passElDef =<< reduce tx
    Defn _ _ (Datatype _ ctors _ _) <- passData  =<< getConstInfo d
    replpas <- (`mkPats` ctors) =<< List.delete sx <$> takenNameStr
    -- make new clauses
    let newpas = [repl sx pa targetPat | pa <- replpas]
    --
    liftIO $ putStrLn $ response $
      L[A"agda2-make-case-action",
        Q $ L $ List.map (A . show . (++ " = ?") . show . ppPa 0) newpas]

  where
  findClause wanted sig = case
       [dropUscore(SI.ConP (qualify mnam dnam) (drop (defFreeVars dbdy) pats))
        |(mnam, md) <- assocs sig
       , (dnam, dbdy) <- assocs $ mdefDefs md
       , Function cls _ <- [theDef dbdy]
       , SI.Clause pats cbdy <- cls
       , MetaV x _ <- [deAbs cbdy]
       , x == wanted ] of
    (h : _ ) -> return h;
    _ -> fail $ "findClause: can't find <clause = " ++ show ii ++ ">"

  mkPats tkn (c:cs) = do (tkn1, pa)<- mkPat tkn c; (pa:)<$> mkPats tkn1 cs

  mkPats tkn []     = return []
  mkPat tkn c = do Defn tc _ (Constructor n _ _) <- getConstInfo c
                   (tkn', pas) <- piToArgPats tkn <$> dePi n tc
                   return (tkn', SI.ConP c pas)
  repl sx replpa = go where
    go pa@(SI.VarP y) | y == sx   = replpa
                      | otherwise = pa
    go (SI.ConP c argpas) = SI.ConP c $ List.map (fmap go) argpas

  dePi 0 t = return t
  dePi i (SI.Pi _ (Abs _ t)) = dePi (i-1) t
  dePi i (SI.Fun _       t)  = dePi (i-1) t
  dePi i t = fail "dePi: not a pi"
 
  piToArgPats tkn t = case t of SI.Pi (Arg h _) (Abs s t) -> go h s   t
                                SI.Fun (Arg h _) t        -> go h "x" t
                                _                         -> (tkn, [])
    where go h ('_':s) t = go h s t
          go h s t = let (tkn1, s1 ) = refreshStr tkn s
                         (tkn2, pas) = piToArgPats tkn1 t
                     in  (tkn2, Arg h (SI.VarP s1) : pas)

  deAbs (Bind (Abs _ b)) = deAbs b
  deAbs (Body t        ) = t

  passAVar e@(SA.Var _ _) = return e
  passAVar x   = fail("passAVar: got "++show x)
  passElDef t@(El(SI.Def _ _) _) = return t
  passElDef t  = fail . ("passElDef: got "++) . show =<< reify t
  passData  d@(Defn _ _ (Datatype _ _ _ _)) = return d
  passData  d  = fail $ "passData: got "++ show d

  dropUscore (SI.VarP ('_':s)) = dropUscore (SI.VarP s)
  dropUscore p@(SI.VarP s) = p
  dropUscore (SI.ConP c apas) = SI.ConP c (List.map (fmap dropUscore) apas)

  -- | To do : precedence of ops
  ppPa prec (SI.VarP n) = P.text n
  ppPa prec (SI.ConP qn []) = P.text (show qn)
  ppPa prec (SI.ConP qn [apa1,apa2])
      | (c:_) <- show qn, not(isAlpha c || c == '_') =
    (if prec > 9 then P.parens else id) $
    ppAPa 10 apa1 P.<+> P.text (show qn) <+> ppAPa 10 apa2
  ppPa prec (SI.ConP qn apas) =
    (if prec > 9 then P.parens else id) $
    P.text (show qn) <+> P.sep (List.map (ppAPa 10) apas)
  ppAPa prec (Arg Hidden pa) = P.braces (ppPa 0 pa)
  ppAPa prec (Arg _      pa) = ppPa prec pa
