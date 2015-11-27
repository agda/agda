{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Agda.TypeChecking.Rules.LHS where

import Prelude hiding (mapM)

import Data.Maybe

import Control.Applicative
import Control.Monad hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Trans.Maybe

import Data.Traversable

import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Syntax.Internal as I hiding (Substitution)
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views (asView)
import Agda.Syntax.Common as Common
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.TypeChecking.Monad

import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.Empty
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (Substitution)
import qualified Agda.TypeChecking.Substitute as S (Substitution)
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Split
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.Data

import Agda.Utils.Except (MonadError(..))
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns.
flexiblePatterns :: [NamedArg A.Pattern] -> TCM FlexibleVars
flexiblePatterns nps = do
  forMaybeM (zip (downFrom $ length nps) nps) $ \ (i, Arg ai p) -> do
    runMaybeT $ (\ f -> FlexibleVar (getHiding ai) f i) <$> maybeFlexiblePattern p

-- | A pattern is flexible if it is dotted or implicit, or a record pattern
--   with only flexible subpatterns.
class IsFlexiblePattern a where
  maybeFlexiblePattern :: a -> MaybeT TCM FlexibleVarKind

  isFlexiblePattern :: a -> TCM Bool
  isFlexiblePattern p = isJust <$> runMaybeT (maybeFlexiblePattern p)

instance IsFlexiblePattern A.Pattern where
  maybeFlexiblePattern p =
    case p of
      A.DotP{}
        -> return DotFlex
      A.WildP{}
        -> return ImplicitFlex
      A.ConP _ (A.AmbQ [c]) qs
        -> ifM (isNothing <$> isRecordConstructor c) mzero {-else-}
             (maybeFlexiblePattern qs)
      _ -> mzero

instance IsFlexiblePattern (I.Pattern' a) where
  maybeFlexiblePattern p =
    case p of
      I.DotP{}  -> return DotFlex
      I.ConP _ i ps
        | Just ConPImplicit <- conPRecord i -> return ImplicitFlex  -- expanded from ImplicitP
        | Just _            <- conPRecord i -> maybeFlexiblePattern ps
        | otherwise -> mzero
      I.VarP{}  -> mzero
      I.LitP{}  -> mzero
      I.ProjP{} -> mzero

-- | Lists of flexible patterns are 'RecordFlex'.
instance IsFlexiblePattern a => IsFlexiblePattern [a] where
  maybeFlexiblePattern ps = RecordFlex <$> mapM maybeFlexiblePattern ps

instance IsFlexiblePattern a => IsFlexiblePattern (Arg a) where
  maybeFlexiblePattern = maybeFlexiblePattern . unArg

instance IsFlexiblePattern a => IsFlexiblePattern (Common.Named name a) where
  maybeFlexiblePattern = maybeFlexiblePattern . namedThing

-- | Compute the dot pattern instantiations.
dotPatternInsts :: [NamedArg A.Pattern] -> Substitution -> [Dom Type] -> TCM [DotPatternInst]
dotPatternInsts ps s as = dpi (map namedArg ps) (reverse s) as
  where
    dpi (_ : _)  []            _       = __IMPOSSIBLE__
    dpi (_ : _)  (Just _ : _)  []      = __IMPOSSIBLE__
    -- the substitution also contains entries for module parameters, so it can
    -- be longer than the pattern
    dpi []       _             _       = return []
    dpi (_ : ps) (Nothing : s) as      = dpi ps s as
    dpi (p : ps) (Just u : s) (a : as) =
      case p of
        A.DotP _ e    -> (DPI e u a :) <$> dpi ps s as
        A.WildP _     -> dpi ps s as
        -- record pattern
        A.ConP _ (A.AmbQ [c]) qs -> do
          Def r es   <- ignoreSharing <$> reduce (unEl $ unDom a)
          let Just vs = allApplyElims es
          (ftel, us) <- etaExpandRecord r vs u
          qs <- insertImplicitPatterns ExpandLast qs ftel
          let instTel EmptyTel _                   = []
              instTel (ExtendTel arg tel) (u : us) = arg : instTel (absApp tel u) us
              instTel ExtendTel{} []               = __IMPOSSIBLE__
              bs0 = instTel ftel (map unArg us)
              -- Andreas, 2012-09-19 propagate relevance info to dot patterns
              bs  = map (mapRelevance (composeRelevance (getRelevance a))) bs0
          dpi (map namedArg qs ++ ps) (map (Just . unArg) us ++ s) (bs ++ as)

        _           -> __IMPOSSIBLE__


-- | In an internal pattern, replace some pattern variables
--   by dot patterns, according to the given substitution.
instantiatePattern
  :: Substitution
     -- ^ Partial substitution for the pattern variables,
     --   given in order of the clause telescope,
     --   (not in the order of occurrence in the patterns).
  -> Permutation
     -- ^ Map from the pattern variables to the telescope variables.
  -> [NamedArg Pattern]
     -- ^ Input patterns.
  -> [NamedArg Pattern]
     -- ^ Output patterns, with some @VarP@ replaced by @DotP@
     --   according to the @Substitution@.
instantiatePattern sub perm ps
  | length sub /= length hps = error $ unlines
      [ "instantiatePattern:"
      , "  sub  = " ++ show sub
      , "  perm = " ++ show perm
      , "  ps   = " ++ show ps
      ]
  | otherwise  = foldr merge ps $ zipWith inst (reverse sub) hps
  where
    -- For each pattern variable get a copy of the patterns
    -- focusing on this variable.
    -- Order them in the dependency (telescope) order.
    hps = permute perm $ allHoles ps
    -- If we do not want to substitute a variable, we
    -- throw away the corresponding one-hole pattern.
    inst Nothing  hps = Nothing
    -- If we want to substitute, we replace the variable
    -- by the dot pattern.
    inst (Just t) hps = Just $ plugHole (DotP t) hps

    -- If we did not instantiate a variable, we can keep the original
    -- patterns in this iteration.
    merge Nothing   ps = ps
    -- Otherwise, we merge the changes in @qs@ into @ps@.
    -- This means we walk simultaneously through @qs@ and @ps@
    -- and expect them to be the same everywhere except that
    -- a @q@ can be a @DotP@ and the corresponding @p@ a @VarP@.
    -- In this case, we take the @DotP@.
    -- Apparently, the other way round can also happen (why?).
    merge (Just qs) ps = zipWith mergeA qs ps
      where
        mergeA a1 a2 = fmap (mergeP (namedArg a1) (namedArg a2) <$) a1

        mergeP (DotP s)  (DotP t)
          | s == t                    = DotP s
          | otherwise                 = __IMPOSSIBLE__
        -- interesting cases:
        mergeP (DotP t)  (VarP _)     = DotP t
        mergeP (VarP _)  (DotP t)     = DotP t
        -- the rest is homomorphical
        mergeP (DotP _)  _            = __IMPOSSIBLE__
        mergeP _         (DotP _)     = __IMPOSSIBLE__
        mergeP (ConP c1 i1 ps) (ConP c2 i2 qs)
          | c1 == c2                  = ConP (c1 `withRangeOf` c2) (mergeCPI i1 i2) $
                                          zipWith mergeA ps qs
          | otherwise                 = __IMPOSSIBLE__
        mergeP (LitP l1) (LitP l2)
          | l1 == l2                  = LitP (l1 `withRangeOf` l2)
          | otherwise                 = __IMPOSSIBLE__
        mergeP (VarP x) (VarP y)
          | x == y                    = VarP x
          | otherwise                 = __IMPOSSIBLE__
        mergeP (ConP _ _ _) (VarP _)  = __IMPOSSIBLE__
        mergeP (ConP _ _ _) (LitP _)  = __IMPOSSIBLE__
        mergeP (VarP _) (ConP _ _ _)  = __IMPOSSIBLE__
        mergeP (VarP _) (LitP _)      = __IMPOSSIBLE__
        mergeP (LitP _) (ConP _ _ _)  = __IMPOSSIBLE__
        mergeP (LitP _) (VarP _)      = __IMPOSSIBLE__
        mergeP (ProjP x) (ProjP y)
          | x == y                    = ProjP x
          | otherwise                 = __IMPOSSIBLE__
        mergeP ProjP{} _              = __IMPOSSIBLE__
        mergeP _       ProjP{}        = __IMPOSSIBLE__

        mergeCPI (ConPatternInfo mr1 mt1) (ConPatternInfo mr2 mt2) =
          ConPatternInfo (mplus mr1 mr2) (mplus mt1 mt2)


-- | In an internal pattern, replace some pattern variables
--   by dot patterns, according to the given substitution.
instantiatePattern'
  :: Substitution
     -- ^ Partial substitution for the pattern variables,
     --   given in order of the clause telescope,
     --   (not in the order of occurrence in the patterns).
  -> Permutation
     -- ^ Map from the pattern variables to the telescope variables.
  -> [NamedArg Pattern]
     -- ^ Input patterns.
  -> [NamedArg Pattern]
     -- ^ Output patterns, with some @VarP@ replaced by @DotP@
     --   according to the @Substitution@.
instantiatePattern' sub perm ps = evalState (mapM goArg ps) 0
  where
    -- get a partial substitution from pattern variables to terms
    sub'    = inversePermute perm sub
    -- get next pattern variable
    next    = do n <- get; put (n+1); return n
    goArg   = traverse goNamed
    goNamed = traverse goPat
    goPat p = case p of
      VarP x       -> replace p
      DotP t       -> replace p
      ConP c mt ps -> ConP c mt <$> mapM goArg ps
      LitP{}       -> return p
      ProjP{}      -> return p
    replace p = do
      i <- next
      let s = case sub' !!! i of
                Nothing -> __IMPOSSIBLE__
                Just s  -> s
      return $ fromMaybe p $ DotP <$> s



-- | Check if a problem is solved. That is, if the patterns are all variables.
isSolvedProblem :: Problem -> Bool
isSolvedProblem problem = null (restPats $ problemRest problem) &&
    all (isSolved . snd . asView . namedArg) (problemInPat problem)
  where
    -- need further splitting:
    isSolved A.ConP{}        = False
    isSolved A.DotP{}        = False
    isSolved A.LitP{}        = False
    isSolved A.DefP{}        = False  -- projection pattern
    isSolved A.RecP{}        = False  -- record pattern
    -- solved:
    isSolved A.VarP{}        = True
    isSolved A.WildP{}       = True
    isSolved A.AbsurdP{}     = True
    -- impossible:
    isSolved A.AsP{}         = __IMPOSSIBLE__  -- removed by asView
    isSolved A.PatternSynP{} = __IMPOSSIBLE__  -- expanded before

-- | For each user-defined pattern variable in the 'Problem', check
-- that the corresponding data type (if any) does not contain a
-- constructor of the same name (which is not in scope); this
-- \"shadowing\" could indicate an error, and is not allowed.
--
-- Precondition: The problem has to be solved.

noShadowingOfConstructors
  :: Call -- ^ Trace, e.g., @CheckPatternShadowing clause@
  -> Problem -> TCM ()
noShadowingOfConstructors mkCall problem =
  traceCall mkCall $ do
    let pat = map (snd . asView . namedArg) $
                  problemInPat problem
        tel = map (unEl . snd . unDom) $ telToList $ problemTel problem
    zipWithM_ noShadowing pat tel -- TODO: does not work for flexible arity and projection patterns
    return ()
  where
  noShadowing (A.WildP     {}) t = return ()
  noShadowing (A.AbsurdP   {}) t = return ()
  noShadowing (A.ConP      {}) t = return ()  -- only happens for eta expanded record patterns
  noShadowing (A.RecP      {}) t = return ()  -- record pattern
  noShadowing (A.DefP      {}) t = return ()  -- projection pattern
  noShadowing (A.AsP       {}) t = __IMPOSSIBLE__
  noShadowing (A.DotP      {}) t = __IMPOSSIBLE__
  noShadowing (A.LitP      {}) t = __IMPOSSIBLE__
  noShadowing (A.PatternSynP {}) t = __IMPOSSIBLE__
  noShadowing (A.VarP x)       t = do
    reportSDoc "tc.lhs.shadow" 30 $ vcat
      [ text $ "checking whether pattern variable " ++ show x ++ " shadows a constructor"
      , nest 2 $ text "type of variable =" <+> prettyTCM t
      ]
    reportSLn "tc.lhs.shadow" 70 $ "  t = " ++ show t
    t <- reduce t
    case t of
      Def t _ -> do
        d <- theDef <$> getConstInfo t
        case d of
          Datatype { dataCons = cs } -> do
            case filter ((A.nameConcrete x ==) . A.nameConcrete . A.qnameName) cs of
              []      -> return ()
              (c : _) -> setCurrentRange x $
                typeError $ PatternShadowsConstructor x c
          Axiom       {} -> return ()
          Function    {} -> return ()
          Record      {} -> return ()
          Constructor {} -> __IMPOSSIBLE__
          Primitive   {} -> __IMPOSSIBLE__
      Var   {} -> return ()
      Pi    {} -> return ()
      Sort  {} -> return ()
      Shared p -> noShadowing (A.VarP x) $ derefPtr p
      MetaV {} -> return ()
      -- TODO: If the type is a meta-variable, should the test be
      -- postponed? If there is a problem, then it will be caught when
      -- the completed module is type checked, so it is safe to skip
      -- the test here. However, users may be annoyed if they get an
      -- error in code which has already passed the type checker.
      Lam   {} -> __IMPOSSIBLE__
      Lit   {} -> __IMPOSSIBLE__
      Level {} -> __IMPOSSIBLE__
      Con   {} -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPatternInst -> TCM ()
checkDotPattern (DPI e v (Dom info a)) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ text "=" <+> prettyTCM v
        , nest 2 $ text ":" <+> prettyTCM a
        ]
  applyRelevanceToContext (argInfoRelevance info) $ do
    u <- checkExpr e a
    -- Should be ok to do noConstraints here
    noConstraints $ equalTerm a u v

-- | Bind the variables in a left hand side and check that 'Hiding' of
--   the patterns matches the hiding info in the type.
--
--   Precondition: the patterns should
--   all be 'A.VarP', 'A.WildP', or 'A.AbsurdP' and the
--   telescope should have the same size as the pattern list.
--   There could also be 'A.ConP's resulting from eta expanded implicit record
--   patterns.
bindLHSVars :: [NamedArg A.Pattern] -> Telescope -> TCM a -> TCM a
bindLHSVars []        tel@ExtendTel{}  _   = do
  reportSDoc "impossible" 10 $
    text "bindLHSVars: no patterns left, but tel =" <+> prettyTCM tel
  __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel         _   = __IMPOSSIBLE__
bindLHSVars []        EmptyTel         ret = ret
bindLHSVars (p : ps) (ExtendTel a tel) ret = do
  unless (getHiding p == getHiding a) $ typeError WrongHidingInLHS
  case namedArg p of
    A.VarP x      -> addContext (x, a) $ bindLHSVars ps (absBody tel) ret
    A.WildP _     -> bindDummy (absName tel)
                 -- @bindDummy underscore@ does not fix issue 819, but
                 -- introduces unwanted underscores in error messages
                 -- (Andreas, 2015-05-28)
    A.AbsurdP pi  -> do
      -- Andreas, 2012-03-15: allow postponement of emptyness check
      isEmptyType (getRange pi) $ unDom a
      -- OLD CODE: isReallyEmptyType $ unArg a
      bindDummy (absName tel)
    A.ConP _ (A.AmbQ [c]) qs -> do -- eta expanded record pattern
      Def r es <- reduce (unEl $ unDom a)
      let Just vs = allApplyElims es
      ftel     <- (`apply` vs) <$> getRecordFieldTypes r
      con      <- getConHead c
      let n   = size ftel
          eta = Con con [ var i <$ (namedThing <$> q) | (q, i) <- zip qs [n - 1, n - 2..0] ]
          -- ^ TODO guilhem
      bindLHSVars (qs ++ ps) (ftel `abstract` absApp (raise (size ftel) tel) eta) ret
    A.ConP{}        -> __IMPOSSIBLE__
    A.RecP{}        -> __IMPOSSIBLE__
    A.DefP{}        -> __IMPOSSIBLE__
    A.AsP{}         -> __IMPOSSIBLE__
    A.DotP{}        -> __IMPOSSIBLE__
    A.LitP{}        -> __IMPOSSIBLE__
    A.PatternSynP{} -> __IMPOSSIBLE__
    where
      bindDummy s = do
        x <- if isUnderscore s then freshNoName_ else freshName_ ("." ++ argNameToString s)
        addContext (x, a) $ bindLHSVars ps (absBody tel) ret

-- | Bind as patterns
bindAsPatterns :: [AsBinding] -> TCM a -> TCM a
bindAsPatterns []                ret = ret
bindAsPatterns (AsB x v a : asb) ret = do
  reportSDoc "tc.lhs.as" 10 $ text "as pattern" <+> prettyTCM x <+>
    sep [ text ":" <+> prettyTCM a
        , text "=" <+> prettyTCM v
        ]
  addLetBinding defaultArgInfo x v a $ bindAsPatterns asb ret

-- | Result of checking the LHS of a clause.
data LHSResult = LHSResult
  { lhsVarTele      :: Telescope
    -- ^ Δ : The types of the pattern variables, in internal dependency order.
    -- Corresponds to 'clauseTel'.
  , lhsPatterns     :: [NamedArg Pattern]
    -- ^ The patterns in internal syntax.
  , lhsBodyType     :: Arg Type
    -- ^ The type of the body. Is @bσ@ if @Γ@ is defined.
    -- 'Irrelevant' to indicate the rhs must be checked in irrelevant mode.
  , lhsPermutation  :: Permutation
    -- ^ The permutation from pattern vars to @Δ@.
    -- Corresponds to 'clausePerm'.
  }

instance InstantiateFull LHSResult where
  instantiateFull' (LHSResult tel ps t perm) = LHSResult
    <$> instantiateFull' tel
    <*> instantiateFull' ps
    <*> instantiateFull' t
    <*> return perm

-- | Check a LHS. Main function.
--
--   @checkLeftHandSide a ps a ret@ checks that user patterns @ps@ eliminate
--   the type @a@ of the defined function, and calls continuation @ret@
--   if successful.

checkLeftHandSide
  :: Call
     -- ^ Trace, e.g. @CheckPatternShadowing clause@
  -> Maybe QName
     -- ^ The name of the definition we are checking.
  -> [NamedArg A.Pattern]
     -- ^ The patterns.
  -> Type
     -- ^ The expected type @a = Γ → b@.
  -> (LHSResult -> TCM a)
     -- ^ Continuation.
  -> TCM a
checkLeftHandSide c f ps a ret = Bench.billTo [Bench.Typing, Bench.CheckLHS] $ do
  problem0 <- problemFromPats ps a
  -- Andreas, 2013-03-15 deactivating the following test allows
  -- flexible arity
  -- unless (noProblemRest problem) $ typeError $ TooManyArgumentsInLHS a

  -- doing the splits:
  LHSState problem@(Problem ps (perm, qs) delta rest) sigma dpi asb
    <- checkLHS f $ LHSState problem0 idS [] []

  unless (null $ restPats rest) $ typeError $ TooManyArgumentsInLHS a

  noShadowingOfConstructors c problem

  noPatternMatchingOnCodata qs

  reportSDoc "tc.lhs.top" 10 $
    vcat [ text "checked lhs:"
         , nest 2 $ vcat
           [ text "ps    = " <+> fsep (map prettyA ps)
           , text "perm  = " <+> text (show perm)
           , text "delta = " <+> prettyTCM delta
           , text "dpi   = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi)
           , text "asb   = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb)
           , text "qs    = " <+> text (show qs)
           ]
         ]

  let b' = restType rest
  bindLHSVars (filter (isNothing . isProjP) ps) delta $ bindAsPatterns asb $ do
    reportSDoc "tc.lhs.top" 10 $ text "bound pattern variables"
    reportSDoc "tc.lhs.top" 10 $ nest 2 $ text "type  = " <+> prettyTCM b'

    -- Check dot patterns
    mapM_ checkDotPattern dpi

    lhsResult <- return $ LHSResult delta qs b' perm
    applyRelevanceToContext (getRelevance b') $ ret lhsResult

-- | The loop (tail-recursive): split at a variable in the problem until problem is solved
checkLHS
  :: Maybe QName       -- ^ The name of the definition we are checking.
  -> LHSState          -- ^ The current state.
  -> TCM LHSState      -- ^ The final state after all splitting is completed
checkLHS f st@(LHSState problem sigma dpi asb) = do

  problem <- insertImplicitProblem problem
  -- Note: inserting implicits no longer preserve solvedness,
  -- since we might insert eta expanded record patterns.
  if isSolvedProblem problem then return $ st { lhsProblem = problem } else do

    unlessM (optPatternMatching <$> gets getPragmaOptions) $
      typeError $ GenericError $ "Pattern matching is disabled"

    foldListT trySplit nothingToSplit $ splitProblem f problem
  where

    nothingToSplit = do
      reportSLn "tc.lhs.split" 50 $ "checkLHS: nothing to split in problem " ++ show problem
      nothingToSplitError problem

    -- Split problem rest (projection pattern, does not fail as there is no call to unifier)

    trySplit (SplitRest projPat projType) _ = do

      -- Compute the new problem
      let Problem ps1 (iperm, ip) delta (ProblemRest (p:ps2) b) = problem
          -- ps'      = ps1 ++ [p]
          ps'      = ps1 -- drop the projection pattern (already splitted)
          rest     = ProblemRest ps2 (projPat $> projType)
          ip'      = ip ++ [fmap (Named Nothing . ProjP) projPat]
          problem' = Problem ps' (iperm, ip') delta rest
      -- Jump the trampolin
      st' <- updateProblemRest (LHSState problem' sigma dpi asb)
      -- If the field is irrelevant, we need to continue in irr. cxt.
      -- (see Issue 939).
      applyRelevanceToContext (getRelevance projPat) $ do
        checkLHS f st'

    -- Split on literal pattern (does not fail as there is no call to unifier)

    trySplit (Split p0 xs (Arg _ (LitFocus lit iph hix a)) p1) _ = do

      -- plug the hole with a lit pattern
      let ip    = plugHole (LitP lit) iph
          iperm = expandP hix 0 $ fst (problemOutPat problem)

      -- substitute the literal in p1 and sigma and dpi and asb
      let delta1 = problemTel p0
          delta2 = absApp (fmap problemTel p1) (Lit lit)
          rho    = singletonS (size delta2) (Lit lit)
          -- Andreas, 2015-06-13 Literals are closed, so need to raise them!
          -- rho    = liftS (size delta2) $ singletonS 0 (Lit lit)
          -- rho    = [ var i | i <- [0..size delta2 - 1] ]
          --       ++ [ raise (size delta2) $ Lit lit ]
          --       ++ [ var i | i <- [size delta2 ..] ]
          sigma'   = applySubst rho sigma
          dpi'     = applySubst rho dpi
          asb0     = applySubst rho asb
          ip'      = applySubst rho ip
          rest'    = applySubst rho (problemRest problem)

      -- Compute the new problem
      let ps'      = problemInPat p0 ++ problemInPat (absBody p1)
          delta'   = abstract delta1 delta2
          problem' = Problem ps' (iperm, ip') delta' rest'
          asb'     = raise (size delta2) (map (\x -> AsB x (Lit lit) a) xs) ++ asb0
      st' <- updateProblemRest (LHSState problem' sigma' dpi' asb')
      checkLHS f st'

    -- Split on constructor pattern (unifier might fail)

    trySplit (Split p0 xs focus@(Arg info Focus{}) p1) tryNextSplit = do
      res <- trySplitConstructor p0 xs focus p1
      case res of
        -- Success.  Continue checking LHS.
        Unifies st'    -> checkLHS f st'
        -- Mismatch.  Report and abort.
        NoUnify  tcerr -> throwError tcerr
        -- Unclear situation.  Try next split.
        -- If no split works, give error from first split.
        -- This is conservative, but might not be the best behavior.
        -- It might be better to collect all the errors and print all of them.
        DontKnow tcerr -> tryNextSplit `catchError` \ _ -> throwError tcerr

    whenUnifies
      :: UnificationResult' a
      -> (a -> TCM (UnificationResult' b))
      -> TCM (UnificationResult' b)
    whenUnifies res cont = do
      case res of
        Unifies a      -> cont a
        NoUnify  tcerr -> return $ NoUnify  tcerr
        DontKnow tcerr -> return $ DontKnow tcerr

    trySplitConstructor p0 xs (Arg info LitFocus{}) p1 = __IMPOSSIBLE__
    trySplitConstructor p0 xs (Arg info
             (Focus { focusCon      = c
                    , focusPatOrigin= porigin
                    , focusConArgs  = qs
                    , focusRange    = r
                    , focusOutPat   = iph
                    , focusHoleIx   = hix
                    , focusDatatype = d
                    , focusParams   = vs
                    , focusIndices  = ws
                    , focusType     = a
                    }
             )) p1 = do
      traceCall (CheckPattern (A.ConP (ConPatInfo porigin $ PatRange r) (A.AmbQ [c]) qs)
                                       (problemTel p0)
                                       (El Prop $ Def d $ map Apply $ vs ++ ws)) $ do

        let delta1 = problemTel p0
        let typeOfSplitVar = Arg info a

        reportSDoc "tc.lhs.split" 10 $ sep
          [ text "checking lhs"
          , nest 2 $ text "tel =" <+> prettyTCM (problemTel problem)
          , nest 2 $ text "rel =" <+> (text $ show $ argInfoRelevance info)
          ]

        reportSDoc "tc.lhs.split" 15 $ sep
          [ text "split problem"
          , nest 2 $ vcat
            [ text "delta1 = " <+> prettyTCM delta1
            , text "typeOfSplitVar =" <+> prettyTCM typeOfSplitVar
            , text "focusOutPat =" <+> (text . show) iph
            , text "delta2 = " <+> prettyTCM (problemTel $ absBody p1)
            ]
          ]

        c <- (`withRangeOf` c) <$> getConForm c
        ca <- defType <$> getConInfo c

        reportSDoc "tc.lhs.split" 20 $ nest 2 $ vcat
          [ text "ca =" <+> prettyTCM ca
          , text "vs =" <+> prettyList (map prettyTCM vs)
          ]

        -- Lookup the type of the constructor at the given parameters
        let a = ca `piApply` vs

        -- It will end in an application of the datatype
        (gamma', ca, d', us) <- do
          TelV gamma' ca@(El _ def) <- telView a
          let Def d' es = ignoreSharing def
              Just us   = allApplyElims es
          return (gamma', ca, d', us)

        -- This should be the same datatype as we split on
        unless (d == d') $ typeError $ ShouldBeApplicationOf ca d'

        -- reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
        --   [ text "gamma' =" <+> text (show gamma')
        --   ]

        -- Andreas 2010-09-07  propagate relevance info to new vars
        let updRel = composeRelevance (getRelevance info)
        gamma' <- return $ mapRelevance updRel <$> gamma'

        -- Insert implicit patterns
        qs' <- insertImplicitPatterns ExpandLast qs gamma'

        unless (size qs' == size gamma') $
          typeError $ WrongNumberOfConstructorArguments (conName c) (size gamma') (size qs')

        let gamma = useNamesFromPattern qs' gamma'

        -- Get the type of the datatype.
        da <- (`piApply` vs) . defType <$> getConstInfo d

        -- Compute the flexible variables
        flex <- flexiblePatterns (problemInPat p0 ++ qs')

        -- Compute the constructor indices by dropping the parameters
        let us' = drop (size vs) us

        reportSDoc "tc.lhs.top" 15 $ addCtxTel delta1 $
          sep [ text "preparing to unify"
              , nest 2 $ vcat
                [ text "c      =" <+> prettyTCM c <+> text ":" <+> prettyTCM a
                , text "d      =" <+> prettyTCM d <+> text ":" <+> prettyTCM da
                , text "gamma  =" <+> prettyTCM gamma
                , text "gamma' =" <+> prettyTCM gamma'
                , text "vs     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM vs)
                , text "us'    =" <+> brackets (fsep $ punctuate comma $ map prettyTCM us')
                , text "ws     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ws)
                ]
              ]

        -- Unify constructor target and given type (in Δ₁Γ)
        res <- addCtxTel (delta1 `abstract` gamma) $
                unifyIndices flex (raise (size gamma) da) us' (raise (size gamma) ws)
        whenUnifies res $ \ sub0 -> do

          -- Andreas 2014-11-25  clear 'Forced' and 'Unused'
          -- Andreas 2015-01-19  ... only after unification
          gamma <- return $ mapRelevance ignoreForced <$> gamma

          -- We should substitute c ys for x in Δ₂ and sigma
          let ys     = teleArgs gamma
              delta2 = absApp (raise (size gamma) $ fmap problemTel p1) (Con c ys)
              rho0   = liftS (size delta2) $ consS (Con c ys) $ raiseS (size gamma)
              -- rho0 = [ var i | i <- [0..size delta2 - 1] ]
              --     ++ [ raise (size delta2) $ Con c ys ]
              --     ++ [ var i | i <- [size delta2 + size gamma ..] ]
              sigma0 = applySubst rho0 sigma
              dpi0   = applySubst rho0 dpi
              asb0   = applySubst rho0 asb
              rest0  = applySubst rho0 (problemRest problem)

          reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma) $ nest 2 $ vcat
            [ text "delta2 =" <+> prettyTCM delta2
            , text "sub0   =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub0)
            ]
          reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma `abstract` delta2) $
            nest 2 $ vcat
              [ text "dpi0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi0)
              , text "asb0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb0)
              ]

          -- Andreas, 2010-09-09, save the type.
          -- It is relative to delta1, but it should be relative to
          -- all variables which will be bound by patterns.
          -- Thus, it has to be raised by 1 (the "hole" variable)
          -- plus the length of delta2 (the variables coming after the hole).
          let storedPatternType = raise (1 + size delta2) typeOfSplitVar
          -- Also remember if we are a record pattern and from an implicit pattern.
          isRec <- isRecord d
          let cpi = ConPatternInfo (isRec $> porigin) (Just storedPatternType)

          -- Plug the hole in the out pattern with c ys
          let ysp = map (argFromDom . fmap (namedVarP . fst)) $ telToList gamma
              ip  = plugHole (ConP c cpi ysp) iph
              ip0 = applySubst rho0 ip

          -- Δ₁Γ ⊢ sub0, we need something in Δ₁ΓΔ₂
          -- Also needs to be padded with Nothing's to have the right length.
          let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
              newTel = problemTel p0 `abstract` (gamma `abstract` delta2)
              sub    = replicate (size delta2) Nothing ++
                       pad (size delta1 + size gamma) (raise (size delta2) sub0) Nothing

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "newTel =" <+> prettyTCM newTel
            , addCtxTel newTel $ text "sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
            , text "ip   =" <+> do prettyList $ map (prettyTCM . namedArg) ip
            , text "ip0  =" <+> do prettyList $ map (prettyTCM . namedArg) ip0
            ]
          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "rho0 =" <+> text (show rho0)
            ]

          -- Instantiate the new telescope with the given substitution
          (delta', perm, rho, instTypes) <- instantiateTel sub newTel


          reportSDoc "tc.lhs.inst" 12 $
            vcat [ sep [ text "instantiateTel"
                       , nest 4 $ brackets $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub
                       , nest 4 $ prettyTCM newTel
                       ]
                 , nest 2 $ text "delta' =" <+> prettyTCM delta'
                 , nest 2 $ text "perm   =" <+> text (show perm)
                 , nest 2 $ text "itypes =" <+> fsep (punctuate comma $ map prettyTCM instTypes)
                 ]

  {-      -- Andreas, 2010-09-09
          -- temporary error message to find non-id perms
          let sorted (Perm _ xs) = xs == List.sort xs
          unless (sorted (perm)) $ typeError $ GenericError $ "detected proper permutation " ++ show perm
  -}
          -- Compute the new dot pattern instantiations
          let ps0'   = problemInPat p0 ++ qs' ++ problemInPat (absBody p1)

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "subst rho sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) (applySubst rho sub))
            , text "ps0'  =" <+> brackets (fsep $ punctuate comma $ map prettyA ps0')
            ]

          newDpi <- dotPatternInsts ps0' (applySubst rho sub) instTypes

          -- The final dpis and asbs are the new ones plus the old ones substituted by ρ
          let dpi' = applySubst rho dpi0 ++ newDpi
              asb' = applySubst rho $ asb0 ++ raise (size delta2) (map (\x -> AsB x (Con c ys) ca) xs)

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "dpi' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi')
            , text "asb' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb')
            ]

          -- Apply the substitution to the type
          let sigma'   = applySubst rho sigma0
              rest'    = applySubst rho rest0

          reportSDoc "tc.lhs.inst" 15 $
            nest 2 $ text "ps0 = " <+> brackets (fsep $ punctuate comma $ map prettyA ps0')

          -- Permute the in patterns
          let ps'  = permute perm ps0'

          -- Compute the new permutation of the out patterns. This is the composition of
          -- the new permutation with the expansion of the old permutation to
          -- reflect the split.
          let perm'  = expandP hix (size gamma) $ fst (problemOutPat problem)
              iperm' = perm `composeP` perm'

          -- Instantiate the out patterns
          let ip'    = instantiatePattern sub perm' ip0
              newip  = applySubst rho ip'

          -- Construct the new problem
          let problem' = Problem ps' (iperm', newip) delta' rest'

          reportSDoc "tc.lhs.top" 12 $ sep
            [ text "new problem"
            , nest 2 $ vcat
              [ text "ps'    = " <+> fsep (map prettyA ps')
              , text "delta' = " <+> prettyTCM delta'
              ]
            ]

          reportSDoc "tc.lhs.top" 14 $ nest 2 $ vcat
            [ text "perm'  =" <+> text (show perm')
            , text "iperm' =" <+> text (show iperm')
            ]
          reportSDoc "tc.lhs.top" 14 $ nest 2 $ vcat
            [ text "ip'    =" <+> prettyList (map (prettyTCM . namedArg) ip')
            , text "newip  =" <+> prettyList (map (prettyTCM . namedArg) newip)
            ]
          reportSDoc "tc.lhs.top" 60 $ nest 2 $ vcat
            [ text "ip'    =" <+> text (show ip')
            , text "newip  =" <+> text (show newip)
            ]

          -- if rest type reduces,
          -- extend the split problem by previously not considered patterns
          st'@(LHSState problem'@(Problem ps' (iperm', ip') delta' rest')
                        sigma' dpi' asb')
            <- updateProblemRest $ LHSState problem' sigma' dpi' asb'

          reportSDoc "tc.lhs.top" 12 $ sep
            [ text "new problem from rest"
            , nest 2 $ vcat
              [ text "ps'    = " <+> fsep (map prettyA ps')
              , text "delta' = " <+> prettyTCM delta'
              , text "ip'    = " <+> prettyList (map (prettyTCM . namedArg) ip')
              , text "iperm' = " <+> text (show iperm')
              ]
            ]
          return $ Unifies st'


-- | Ensures that we are not performing pattern matching on codata.

noPatternMatchingOnCodata :: [NamedArg Pattern] -> TCM ()
noPatternMatchingOnCodata = mapM_ (check . namedArg)
  where
  check (VarP {})   = return ()
  check (DotP {})   = return ()
  check (ProjP{})   = return ()
  check (LitP {})   = return ()  -- Literals are assumed not to be coinductive.
  check (ConP con _ ps) = do
    TelV _ t <- telView' . defType <$> do getConstInfo $ conName con
    c <- isCoinductive t
    case c of
      Nothing    -> __IMPOSSIBLE__
      Just False -> mapM_ (check . namedArg) ps
      Just True  -> typeError $
        GenericError "Pattern matching on coinductive types is not allowed"
