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
import TypeChecking.Errors

import Syntax.Position
import Syntax.Parser
import Syntax.Concrete as SC
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
  Right (a,st',ss') <- runTCM $ do
      putUndoStack us
      put st
      x <- withEnv env cmd
      st <- get
      us <- getUndoStack
      return (x,st,us)
    `catchError` \err -> do
	s <- prettyError err
	liftIO $ putStrLn s
	liftIO $ exitWith $ ExitFailure 1
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
cmd_refine = give_gen B.refine $ \s -> emacsStr . show

give_gen give_ref mk_newtxt ii rng s = crashOnException $ ioTCM $ do
    prec      <- contextPrecedence <$> getInteractionScope ii
    (ae, iis) <- give_ref ii Nothing =<< parseExprIn ii rng s
    let newtxt = A . mk_newtxt s $ abstractToConcreteCtx prec ae
        newgs  = Q . L $ List.map showNumIId iis
    liftIO $ putStrLn $ response $
           L[A"agda2-give-action", showNumIId ii, newtxt, newgs]

parseExprIn :: InteractionId -> Range -> String -> TCM SA.Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaRange mId rng       
    mi  <- getMetaInfo <$> lookupMeta mId
    i   <- fresh
    liftIO $ concreteToAbstract
             (ScopeState {freshId = i})
             (clScope mi)
             (parsePosString exprParser (rStart (getRange mi)) s)

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
  ex  <- passAVar =<< parseExprIn ii rng s -- the pattern variable to case on
  let sx = show ex
  -- find the clause to refine
  targetPat <- findClause mId =<< getSignature -- not the metaSig.
  withMetaInfo mfo $ do
    -- gather constructors for ex
    (vx,tx) <- inferExpr ex
    El(SI.Def d _) _ <- passElDef =<< reduce tx
    Defn _ _ (Datatype _ ctors _ _) <- passData =<< getConstInfo d
    replpas <- (`mkPats` ctors) =<< List.delete sx <$> takenNameStr
    -- make new clauses
    let newpas = [repl sx pa targetPat | pa <- replpas]
    --
    liftIO $ putStrLn $ response $
      L[A"agda2-make-case-action",
        Q $ L $ List.map (A . emacsStr . (++ " = ?") . show . ppPa 0) newpas]

  where
  findClause wanted sig = case
       [dropUscore(SI.ConP (SI.qualify mnam dnam)
                   (drop (defFreeVars dbdy) pats))
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


cmd_solveAll :: IO ()
cmd_solveAll = crashOnException $ ioTCM $ do
    out <- getInsts =<< gets stInteractionPoints
    liftIO $ putStrLn $ response $
      L[ A"agda2-solveAll-action" , Q . L $ concatMap prn out]
  where
  getInsts = Map.foldWithKey go (return []) where
    go ii mi rest = do
      mv <- lookupMeta mi
      withMetaInfo (getMetaInfo mv) $ do    
        args <- allCtxVars
        let out m = do e <- lowerMeta . abstractToConcrete_ <$> reify m;
                       ((ii, e):) <$> rest
        case mvInstantiation mv of InstV _  -> out (MetaV mi args)
                                   InstT _  -> out (MetaT mi args)
                                   InstS _  -> out (MetaS mi)
                                   TM.Open  -> rest
  prn (ii,e)= [showNumIId ii, A $ emacsStr $ show e]

class LowerMeta a where lowerMeta :: a -> a
instance LowerMeta SC.Expr where
  lowerMeta = go where
    go e = case e of
      Ident _              -> e
      SC.Lit _             -> e
      SC.QuestionMark _ _  -> preMeta
      SC.Underscore _ _    -> preUscore
      SC.App r e1 ae2      -> case appView e of
        SC.AppView (SC.QuestionMark _ _) _ -> preMeta
        SC.AppView (SC.Underscore   _ _) _ -> preUscore
        _ -> SC.App r (go e1) (lowerMeta ae2)
      InfixApp e1 qn e2    -> InfixApp (go e1) qn (go e2)
      SC.Lam r bs e1       -> SC.Lam r (lowerMeta bs) (go e1)
      SC.Fun r ae1 e2      -> SC.Fun r (lowerMeta ae1) (go e2)
      SC.Pi tb e1          -> SC.Pi (lowerMeta tb) (go e1)
      SC.Set _             -> e
      SC.Prop _            -> e
      SC.SetN _ _          -> e
      SC.Let r ds e1       -> SC.Let r (lowerMeta ds) (go e1)
      Paren r e1           -> case go e1 of
        q@(SC.QuestionMark _ Nothing) -> q
        e2                            -> Paren r e2
      Absurd _          -> e
      As r n e1         -> As r n (go e1)

instance LowerMeta SC.LamBinding where
  lowerMeta b@(SC.DomainFree _ _) = b
  lowerMeta (SC.DomainFull tb)    = SC.DomainFull (lowerMeta tb)

instance LowerMeta SC.TypedBindings where
  lowerMeta (SC.TypedBindings r h bs) = SC.TypedBindings r h (lowerMeta bs)

instance LowerMeta SC.TypedBinding where
  lowerMeta (SC.TBind r ns e) = SC.TBind r ns (lowerMeta e)
  lowerMeta (SC.TNoBind e)    = SC.TNoBind (lowerMeta e)

instance LowerMeta SC.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig n e1            -> TypeSig n (lowerMeta e1)
      FunClause lhs rhs whcl  -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      Data r n tel e1 cs      -> Data r n
                                 (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      Infix _ _               -> d
      Mutual r ds             -> Mutual r (lowerMeta ds)
      Abstract r ds           -> Abstract r (lowerMeta ds)
      Private r ds            -> Private r (lowerMeta ds)
      Postulate r sigs        -> Postulate r (lowerMeta sigs)
      SC.Open _ _ _           -> d
      SC.Import _ _ _ _       -> d
      ModuleMacro r n tel e1 dir -> ModuleMacro r n
                                    (lowerMeta tel) (lowerMeta e1) dir
      SC.Module r qn tel ds   -> SC.Module r qn (lowerMeta tel) (lowerMeta ds)
      
instance LowerMeta a => LowerMeta [a] where
  lowerMeta as = List.map lowerMeta as

instance LowerMeta a => LowerMeta (Arg a) where
  lowerMeta aa = fmap lowerMeta aa


preMeta   = SC.QuestionMark noRange Nothing
preUscore = SC.Underscore   noRange Nothing

cmd_compute :: B.Rewrite -> GoalCommand
cmd_compute _ ii rng s = crashOnException $ 
  putStrLn . show =<< ioTCM (B.evalInMeta ii =<< parseExprIn ii rng s)

-- change "\<decimal>" to "\x<hex>"
emacsStr s = go (show s) where
  go ('\\':(a:b:c:t))
     | all isDigit [a,b,c] = "\\x" ++ hex8(read [a,b,c]::Int) ++ go t
  go (c:s) = c : go s
  go []    = []
  hex8 n = let (h,l) = quotRem n 16 in [d h, d l]
  d i = (['0'..'9'] ++ ['a'..'f'])!! i
