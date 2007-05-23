{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances #-}

module Interaction.GhciTop
  ( module Interaction.GhciTop
  , module TypeChecker
  , module TM
  , module TypeChecking.MetaVars
  , module TypeChecking.Reduce
  , module TypeChecking.Errors

  , module Syntax.Position
  , module Syntax.Parser
  , module SCo
--  , module SC  -- trivial clash removal: remove all!
--  , module SA
--  , module SI
  , module Syntax.Scope.Base
  , module Syntax.Scope.Monad
  , module Info
  , module Syntax.Translation.ConcreteToAbstract
  , module Syntax.Translation.AbstractToConcrete
  , module Syntax.Translation.InternalToAbstract
  , module Syntax.Abstract.Name

  , module Interaction.Exceptions
  , module B
  , module CL
  )
  where

import Prelude hiding (print, putStr, putStrLn)
import System.IO hiding (print, putStr, putStrLn)
import System.Directory
import System.IO.Unsafe
import Data.Char
import Data.IORef
import qualified Text.PrettyPrint as P

import Utils.Fresh
import Utils.Monad
import Utils.Monad.Undo
import Utils.IO
import Utils.Pretty
import Utils.String
import Utils.FileName
import Utils.Tuple

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Exception
import Data.List as List
import Data.Map as Map
import System.Exit

import TypeChecker
import TypeChecking.Monad as TM
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Errors

import Syntax.Position
import Syntax.Parser
import Syntax.Concrete as SC
import Syntax.Common as SCo
import Syntax.Concrete.Name as CN
import Syntax.Concrete.Pretty ()
import Syntax.Abstract as SA
import Syntax.Abstract.Pretty
import Syntax.Internal as SI
import Syntax.Scope.Base
import Syntax.Scope.Monad hiding (bindName)
import qualified Syntax.Info as Info
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete hiding (withScope)
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Name

import Interaction.Exceptions
import qualified Interaction.BasicOps as B
import qualified Interaction.CommandLine.CommandLine as CL
import Interaction.Highlighting.Precise (File)
import Interaction.Highlighting.Generate
import Interaction.Highlighting.Emacs

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
  r   <- runTCM $ do
      putUndoStack us
      put st
      x <- withEnv env cmd
      st <- get
      us <- getUndoStack
      return (x,st,us)
    `catchError` \err -> do
	s <- prettyError err
        liftIO $ outputErrorInfo (getRange err) s
	liftIO $ display_info "*Error*" s
	fail "exit"
  case r of
    Right (a,st',ss') -> do
      writeIORef theTCState st'
      writeIORef theUndoStack ss'
      return a
    Left _ -> exitWith $ ExitFailure 1

-- | Set the current working directory based on the file name of the
-- current module and its module name, so that when the module is
-- imported qualified it will be found.
--
-- The path is assumed to be absolute.
--
-- The given list of declarations should correspond to a module, i.e.
-- it should be non-empty and the last declaration should be
-- 'SC.Module' something.

setWorkingDirectory :: FilePath -> [SC.Declaration] -> IO ()
setWorkingDirectory _    [] = __IMPOSSIBLE__
setWorkingDirectory file xs = case last xs of
  SC.Module _ n _ _ -> setCurrentDirectory (newDir $ countDots n)
  _                 -> __IMPOSSIBLE__
  where
  countDots (SC.QName _)  = 0
  countDots (SC.Qual _ n) = 1 + countDots n

  (path, _, _) = splitFilePath file
  newDir n     = dropDirectory n path

cmd_load :: String -> IO ()
cmd_load file = infoOnException $ do
    (pragmas, m) <- parseFile' moduleParser file
    setWorkingDirectory file m
    (is, syntaxInfo) <- ioTCM $ do
	    resetState
	    pragmas  <- concreteToAbstract_ pragmas	-- identity for top-level pragmas at the moment
	    topLevel <- concreteToAbstract_ (TopLevel m)
	    setUndo
	    setOptionsFromPragmas pragmas
	    checkDecls $ topLevelDecls topLevel
	    setScope $ outsideScope topLevel
	    is <- lispIP
            tokens <- liftIO $ parseFile' tokensParser file
            syntaxInfo <- generateSyntaxInfo tokens topLevel
            return (is, syntaxInfo)
    -- Currently highlighting information is only generated when a
    -- file is loaded, or an error is encountered.
    outputSyntaxInfo file syntaxInfo

    -- The Emacs mode uses two different annotation mechanisms, and
    -- they cannot be invoked in any order. The one triggered by the
    -- following line has to be run after the one triggered by
    -- outputSyntaxInfo.
    putStrLn $ response $ L [A "agda2-load-action", is]
    cmd_metas
  where lispIP  = format . sortRng <$> (tagRng =<< getInteractionPoints)
        tagRng  = mapM (\i -> (,)i <$> getInteractionRange i)
        sortRng = sortBy ((.snd) . compare . snd)
        format  = Q . L . List.map (A . tail . show . fst)

cmd_constraints :: IO ()
cmd_constraints = infoOnException $ ioTCM $ do
    cs <- mapM showA =<< B.getConstraints
    liftIO $ display_info "*Constraints*" (unlines cs)


cmd_metas :: IO ()
cmd_metas = infoOnException $ ioTCM $ do -- CL.showMetas []
  (ims, hms) <- B.typeOfMetas B.AsIs
  di <- mapM showA ims
  dh <- mapM showA hms
  liftIO $ display_info "*All Goals*" $ unlines $
    di ++ dh

cmd_undo :: IO ()
cmd_undo = ioTCM undo

cmd_reset :: IO ()
cmd_reset = ioTCM $ do putUndoStack []; resetState

type GoalCommand = InteractionId -> Range -> String -> IO()

cmd_give :: GoalCommand
cmd_give = give_gen B.give $ \s ce -> case ce of (SC.Paren _ _)-> "'paren"
                                                 _             -> "'no-paren"

cmd_refine :: GoalCommand
cmd_refine = give_gen B.refine $ \s -> emacsStr . show

give_gen give_ref mk_newtxt ii rng s = infoOnException $ do
    ioTCM $ do
      prec      <- scopePrecedence <$> getInteractionScope ii
      (ae, iis) <- give_ref ii Nothing =<< parseExprIn ii rng s
      newtxt <- A . mk_newtxt s <$> abstractToConcreteCtx prec ae
      let newgs  = Q . L $ List.map showNumIId iis
      liftIO $ putStrLn $ response $
                 L[A"agda2-give-action", showNumIId ii, newtxt, newgs]
    cmd_metas

parseExprIn :: InteractionId -> Range -> String -> TCM SA.Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaVarRange mId rng       
    mi  <- getMetaInfo <$> lookupMeta mId
    e <- liftIO $ parsePosString exprParser (rStart (getRange mi)) s
    concreteToAbstract (clScope mi) e

cmd_context :: GoalCommand
cmd_context ii _ _ = infoOnException $ do
  display_info "*Context*" . unlines
      =<< ioTCM (mapM showA =<< B.contextOfMeta ii)

cmd_infer :: B.Rewrite -> GoalCommand
cmd_infer norm ii rng s = infoOnException $ do
  display_info "*Inferred Type*"
      =<< ioTCM (showA =<< B.typeInMeta ii norm =<< parseExprIn ii rng s)


cmd_goal_type :: B.Rewrite -> GoalCommand
cmd_goal_type norm ii _ _ = infoOnException $ do 
    display_info "*Current Goal*" =<< ioTCM (showA =<< B.typeOfMeta norm ii)

display_info :: String -> String -> IO()
display_info bufname content =
  putStrLn . response
    $ L[A"agda2-info-action", A(quote bufname),  A(quote content)]

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

takenNameStr :: TCM [String]
takenNameStr = do
  xss <- sequence [ List.map (fst . unArg) <$> getContext
                  , keys <$> asks envLetBindings
                  , List.map qnameName . keys . sigDefinitions <$> getSignature
		  ]
  return $ concat [ parts $ nameConcrete x | x <- concat xss]
  where
    parts x = [ s | Id _ s <- nameParts x ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]

cmd_make_case :: GoalCommand
cmd_make_case ii rng s = infoOnException $ ioTCM $ do
  mId <- lookupInteractionId ii
  mfo <- getMetaInfo <$> lookupMeta mId
  ex  <- passAVar =<< parseExprIn ii rng s -- the pattern variable to case on
  sx  <- showA ex
  -- find the clause to refine
  targetPat <- findClause mId =<< getSignature -- not the metaSig.
  withMetaInfo mfo $ do
    -- gather constructors for ex
    (vx,tx) <- inferExpr ex
    El _ (SI.Def d _) <- passElDef =<< reduce tx
    Defn _ _ (Datatype _ _ _ ctors _ _) <- passData =<< getConstInfo d
    replpas <- (`mkPats` ctors) =<< List.delete sx <$> takenNameStr
    -- make new clauses
    let newpas = [repl sx pa targetPat | pa <- replpas]
    --
    liftIO $ putStrLn $ response $
      L[A"agda2-make-case-action",
        Q $ L $ List.map (A . quote . (++ " = ?") . show . ppPa 0) newpas]

  where
  findClause wanted sig = do
    let defFree (x, d) = do
	  n <- getDefFreeVars x
	  return (x, n, d)
    xs <- mapM defFree $ assocs $ sigDefinitions sig
    case
       [dropUscore(SI.ConP dnam
                   (drop n pats))
       | (dnam, n, dbdy) <- xs
       , Function cls _ <- [theDef dbdy]
       , SI.Clause pats cbdy <- cls
       , Just (MetaV x _) <- [deAbs cbdy]
       , x == wanted ] of
      (h : _ ) -> return h
      _ -> fail $ "findClause: can't find <clause = " ++ show ii ++ ">"

  mkPats tkn (c:cs) = do (tkn1, pa)<- mkPat tkn c; (pa:)<$> mkPats tkn1 cs

  mkPats tkn []     = return []
  mkPat tkn c = do Defn _ tc (Constructor n _ _ _) <- getConstInfo c
                   (tkn', pas) <- piToArgPats tkn <$> dePi n tc
                   return (tkn', SI.ConP c pas)
  repl sx replpa = go where
    go pa@(SI.VarP y) | y == sx   = replpa
                      | otherwise = pa
    go (SI.ConP c argpas) = SI.ConP c $ List.map (fmap go) argpas
    go (SI.LitP l)	  = SI.LitP l

  dePi 0 t = return t
  dePi i (El _ (SI.Pi _ (Abs _ t))) = dePi (i-1) t
  dePi i (El _ (SI.Fun _       t))  = dePi (i-1) t
  dePi i t = fail "dePi: not a pi"
 
  piToArgPats tkn t = case unEl t of
    SI.Pi (Arg h _) (Abs s t) -> go h s   t
    SI.Fun (Arg h _) t        -> go h "x" t
    _                         -> (tkn, [])
    where go h ('_':s) t = go h s t
          go h s t = let (tkn1, s1 ) = refreshStr tkn s
                         (tkn2, pas) = piToArgPats tkn1 t
                     in  (tkn2, Arg h (SI.VarP s1) : pas)

  deAbs (Bind (Abs _ b)) = deAbs b
  deAbs (NoBind b)	 = deAbs b
  deAbs (Body t        ) = Just t
  deAbs  NoBody		 = Nothing

  passAVar e@(SA.Var _) = return e
  passAVar x   = fail . ("passAVar: got "++) =<< showA x
  passElDef t@(El _ (SI.Def _ _)) = return t
  passElDef t  = fail . ("passElDef: got "++) =<< showA =<< reify t
  passData  d@(Defn _ _ (Datatype _ _ _ _ _ _))  = return d
  passData  d@(Defn _ _ (TM.Record _ _ _ _ _ _)) = fail $ "passData: got record"
  passData  d@(Defn _ _ (Function _ _))		 = fail $ "passData: got function"
  passData  d@(Defn _ _ TM.Axiom)		 = fail $ "passData: got axiom"
  passData  d@(Defn _ _ (Constructor _ _ _ _))	 = fail $ "passData: got constructor"
  passData  d@(Defn _ _ (TM.Primitive _ _ _))	 = fail $ "passData: got primitive"

  dropUscore (SI.VarP ('_':s)) = dropUscore (SI.VarP s)
  dropUscore p@(SI.VarP s) = p
  dropUscore (SI.ConP c apas) = SI.ConP c (List.map (fmap dropUscore) apas)
  dropUscore (SI.LitP l) = SI.LitP l

  -- | To do : precedence of ops
  ppPa prec (SI.VarP n) = P.text n
  ppPa prec (SI.LitP l) = pretty l
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
cmd_solveAll = infoOnException $ ioTCM $ do
    out <- getInsts =<< gets stInteractionPoints
    liftIO $ putStrLn $ response $
      L[ A"agda2-solveAll-action" , Q . L $ concatMap prn out]
  where
  getInsts = Map.foldWithKey go (return []) where
    go :: InteractionId -> MetaId -> TCM [(InteractionId, SC.Expr)] -> TCM [(InteractionId, SC.Expr)]
    go ii mi rest = do
      mv <- lookupMeta mi
      withMetaInfo (getMetaInfo mv) $ do    
        args <- getContextArgs
        let out m = do e <- lowerMeta <$> (abstractToConcrete_ =<< reify m)
                       ((ii, e):) <$> rest
        case mvInstantiation mv of InstV _	  -> out (MetaV mi args)
                                   InstS _	  -> out (MetaS mi)
                                   TM.Open	  -> rest
				   BlockedConst _ -> rest
				   FirstOrder	  -> rest
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
      SC.Dot r e	-> SC.Dot r (go e)
      SC.RawApp r es	-> SC.RawApp r (lowerMeta es)
      SC.OpApp r x es	-> SC.OpApp r x (lowerMeta es)
      SC.Rec r fs	-> SC.Rec r (List.map (id -*- lowerMeta) fs)
      SC.HiddenArg r e	-> SC.HiddenArg r (lowerMeta e)

instance LowerMeta SC.LamBinding where
  lowerMeta b@(SC.DomainFree _ _) = b
  lowerMeta (SC.DomainFull tb)    = SC.DomainFull (lowerMeta tb)

instance LowerMeta SC.TypedBindings where
  lowerMeta (SC.TypedBindings r h bs) = SC.TypedBindings r h (lowerMeta bs)

instance LowerMeta SC.TypedBinding where
  lowerMeta (SC.TBind r ns e) = SC.TBind r ns (lowerMeta e)
  lowerMeta (SC.TNoBind e)    = SC.TNoBind (lowerMeta e)

instance LowerMeta SC.RHS where
    lowerMeta (SC.RHS e) = SC.RHS (lowerMeta e)
    lowerMeta  SC.AbsurdRHS = SC.AbsurdRHS

instance LowerMeta SC.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig n e1            -> TypeSig n (lowerMeta e1)
      FunClause lhs rhs whcl  -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      Data r n tel e1 cs      -> Data r n
                                 (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      SC.Record r n tel e1 cs -> SC.Record r n
                                 (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      Infix _ _               -> d
      Mutual r ds             -> Mutual r (lowerMeta ds)
      Abstract r ds           -> Abstract r (lowerMeta ds)
      Private r ds            -> Private r (lowerMeta ds)
      Postulate r sigs        -> Postulate r (lowerMeta sigs)
      SC.Primitive r sigs     -> SC.Primitive r (lowerMeta sigs)
      SC.Open _ _ _           -> d
      SC.Import _ _ _ _ _     -> d
      SC.Pragma _	      -> d
      ModuleMacro r n tel e1 op dir -> ModuleMacro r n
                                    (lowerMeta tel) (lowerMeta e1) op dir
      SC.Module r qn tel ds   -> SC.Module r qn (lowerMeta tel) (lowerMeta ds)

instance LowerMeta SC.WhereClause where
  lowerMeta SC.NoWhere		= SC.NoWhere
  lowerMeta (SC.AnyWhere ds)	= SC.AnyWhere $ lowerMeta ds
  lowerMeta (SC.SomeWhere m ds) = SC.SomeWhere m $ lowerMeta ds

instance LowerMeta a => LowerMeta [a] where
  lowerMeta as = List.map lowerMeta as

instance LowerMeta a => LowerMeta (Arg a) where
  lowerMeta aa = fmap lowerMeta aa

instance LowerMeta a => LowerMeta (Named name a) where
  lowerMeta aa = fmap lowerMeta aa


preMeta   = SC.QuestionMark noRange Nothing
preUscore = SC.Underscore   noRange Nothing

cmd_compute :: B.Rewrite -> GoalCommand
cmd_compute _ ii rng s = infoOnException $ do
  v <- ioTCM (prettyA =<< B.evalInMeta ii =<< parseExprIn ii rng s)
  display_info "*Normal Form*" (show v)

-- change "\<decimal>" to a single character
-- TODO: This seems to be the wrong solution to the problem. Attack
-- the source instead.
emacsStr s = go (show s) where
  go ('\\':ns@(n:_))
     | isDigit n = toEnum (read digits :: Int) : go rest
     where (digits, rest) = span isDigit ns
  go (c:s) = c : go s
  go []    = []


infoOnException m = failOnException inform m where
  inform rng msg = do
    outputErrorInfo rng msg
    display_info "*Error*" $ unlines [show rng ++ " : ", msg]
    exitWith (ExitFailure 1)

------------------------------------------------------------------------
-- Syntax highlighting

-- | Output syntax highlighting information for the given file, and
-- tell the Emacs mode to reload the highlighting information.

outputSyntaxInfo :: FilePath -> File -> IO ()
outputSyntaxInfo file syntaxInfo = do
    writeSyntaxInfo file syntaxInfo
    putStrLn $ response $ L [A "agda2-highlight-reload"]

-- | Output syntax highlighting information for the given error
-- (represented as a range and a string), and tell the Emacs mode to
-- reload the highlighting information and go to the first error
-- position.

outputErrorInfo :: Range -> String -> IO ()
outputErrorInfo r s = do
  case mFile of
    Nothing   -> return ()
    Just file -> outputSyntaxInfo file info
  case mInitialPos of
    Nothing     -> return ()
    Just (f, p) -> putStrLn $ response $
                 L [A "annotation-goto", Q $ L [A (show f), A (show p)]]
  where
  (mFile, info) = generateErrorInfo r s

  mInitialPos = case rStart r of
    NoPos                          -> Nothing
    Pn { srcFile = f, posPos = p } -> Just (f, p)
