{-# LANGUAGE NondecreasingIndentation #-}

-- | Unification algorithm for specializing datatype indices, as described in
--     \"Unifiers as Equivalences: Proof-Relevant Unification of Dependently
--     Typed Data\" by Jesper Cockx, Dominique Devriese, and Frank Piessens
--     (ICFP 2016).
--
--   This is the unification algorithm used for checking the left-hand side
--   of clauses (see @Agda.TypeChecking.Rules.LHS@), coverage checking (see
--   @Agda.TypeChecking.Coverage@) and indirectly also for interactive case
--   splitting (see @Agda.Interaction.MakeCase@).
--
--   A unification problem (of type @UnifyState@) consists of:
--
--   1. A telescope @varTel@ of free variables, some or all of which are
--      flexible (as indicated by @flexVars@).
--
--   2. A telescope @eqTel@ containing the types of the equations.
--
--   3. Left- and right-hand sides for each equation:
--      @varTel ⊢ eqLHS : eqTel@ and @varTel ⊢ eqRHS : eqTel@.
--
--   The unification algorithm can end in three different ways:
--   (type @UnificationResult@):
--
--   - A *positive success* @Unifies (tel, sigma, ps)@ with @tel ⊢ sigma : varTel@,
--     @tel ⊢ eqLHS [ varTel ↦ sigma ] ≡ eqRHS [ varTel ↦ sigma ] : eqTel@,
--     and @tel ⊢ ps : eqTel@. In this case, @sigma;ps@ is an *equivalence*
--     between the telescopes @tel@ and @varTel(eqLHS ≡ eqRHS)@.
--
--   - A *negative success* @NoUnify err@ means that a conflicting equation
--     was found (e.g an equation between two distinct constructors or a cycle).
--
--   - A *failure* @UnifyStuck err@ means that the unifier got stuck.
--
--   The unification algorithm itself consists of two parts:
--
--   1. A *unification strategy* takes a unification problem and produces a
--      list of suggested unification rules (of type @UnifyStep@). Strategies
--      can be constructed by composing simpler strategies (see for example the
--      definition of @completeStrategyAt@).
--
--   2. The *unification engine* @unifyStep@ takes a unification rule and tries
--      to apply it to the given state, writing the result to the UnifyOutput
--      on a success.
--
--   The unification steps (of type @UnifyStep@) are the following:
--
--   - *Deletion* removes a reflexive equation @u =?= v : a@ if the left- and
--     right-hand side @u@ and @v@ are (definitionally) equal. This rule results
--     in a failure if --without-K is enabled (see \"Pattern Matching Without K\"
--     by Jesper Cockx, Dominique Devriese, and Frank Piessens (ICFP 2014).
--
--   - *Solution* solves an equation if one side is (eta-equivalent to) a
--     flexible variable. In case both sides are flexible variables, the
--     unification strategy makes a choice according to the @chooseFlex@
--     function in @Agda.TypeChecking.Rules.LHS.Problem@.
--
--   - *Injectivity* decomposes an equation of the form
--     @c us =?= c vs : D pars is@ where @c : Δc → D pars js@ is a constructor
--     of the inductive datatype @D@ into a sequence of equations
--     @us =?= vs : delta@. In case @D@ is an indexed datatype,
--     *higher-dimensional unification* is applied (see below).
--
--   - *Conflict* detects absurd equations of the form
--     @c₁ us =?= c₂ vs : D pars is@ where @c₁@ and @c₂@ are two distinct
--     constructors of the datatype @D@.
--
--   - *Cycle* detects absurd equations of the form @x =?= v : D pars is@ where
--     @x@ is a variable of the datatype @D@ that occurs strongly rigid in @v@.
--
--   - *EtaExpandVar* eta-expands a single flexible variable @x : R@ where @R@
--     is a (eta-expandable) record type, replacing it by one variable for each
--     field of @R@.
--
--   - *EtaExpandEquation* eta-expands an equation @u =?= v : R@ where @R@ is a
--     (eta-expandable) record type, replacing it by one equation for each field
--     of @R@. The left- and right-hand sides of these equations are the
--     projections of @u@ and @v@.
--
--   - *LitConflict* detects absurd equations of the form @l₁ =?= l₂ : A@ where
--     @l₁@ and @l₂@ are distinct literal terms.
--
--   - *StripSizeSuc* simplifies an equation of the form
--     @sizeSuc x =?= sizeSuc y : Size@ to @x =?= y : Size@.
--
--   - *SkipIrrelevantEquation@ removes an equation between irrelevant terms.
--
--   - *TypeConInjectivity* decomposes an equation of the form
--     @D us =?= D vs : Set i@ where @D@ is a datatype. This rule is only used
--     if --injective-type-constructors is enabled.
--
--   Higher-dimensional unification (new, does not yet appear in any paper):
--   If an equation of the form @c us =?= c vs : D pars is@ is encountered where
--   @c : Δc → D pars js@ is a constructor of an indexed datatype
--   @D pars : Φ → Set ℓ@, it is in general unsound to just simplify this
--   equation to @us =?= vs : Δc@. For this reason, the injectivity rule in the
--   paper restricts the indices @is@ to be distinct variables that are bound in
--   the telescope @eqTel@. But we can be more general by introducing new
--   variables @ks@ to the telescope @eqTel@ and equating these to @is@:
--   @
--       Δ₁(x : D pars is)Δ₂
--        ≃
--       Δ₁(ks : Φ)(x : D pars ks)(ps : is ≡Φ ks)Δ₂
--   @
--   Since @ks@ are distinct variables, it's now possible to apply injectivity
--   to the equation @x@, resulting in the following new equation telescope:
--   @
--     Δ₁(ys : Δc)(ps : is ≡Φ js[Δc ↦ ys])Δ₂
--   @
--   Now we can solve the equations @ps@ by recursively calling the unification
--   algorithm with flexible variables @Δ₁(ys : Δc)@. This is called
--   *higher-dimensional unification* since we are unifying equality proofs
--   rather than terms. If the higher-dimensional unification succeeds, the
--   resulting telescope serves as the new equation telescope for the original
--   unification problem.

module Agda.TypeChecking.Rules.LHS.Unify
  ( UnificationResult
  , UnificationResult'(..)
  , NoLeftInv(..)
  , unifyIndices'
  , unifyIndices ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer (WriterT(..), MonadWriter(..))
import Control.Monad.Except

import Data.Semigroup hiding (Arg)
import qualified Data.List as List
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import qualified Agda.Benchmarking as Bench

import Agda.Interaction.Options (optInjectiveTypeConstructors, optCubical, optWithoutK)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Builtin -- (constructorForm, getTerm, builtinPathP)
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Names
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Patterns.Match as Match
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Precompute
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Records

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Unify.Types
import Agda.TypeChecking.Rules.LHS.Unify.LeftInverse

import Agda.Utils.Empty
import Agda.Utils.Benchmark
import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.WithDefault
import Agda.Utils.Tuple

import Agda.Utils.Impossible


-- | Result of 'unifyIndices'.
type UnificationResult = UnificationResult'
  ( Telescope                  -- @tel@
  , PatternSubstitution        -- @sigma@ s.t. @tel ⊢ sigma : varTel@
  , [NamedArg DeBruijnPattern] -- @ps@    s.t. @tel ⊢ ps    : eqTel @
  )

type FullUnificationResult = UnificationResult'
  ( Telescope                  -- @tel@
  , PatternSubstitution        -- @sigma@ s.t. @tel ⊢ sigma : varTel@
  , [NamedArg DeBruijnPattern] -- @ps@    s.t. @tel ⊢ ps    : eqTel @
  , Either NoLeftInv (Substitution, Substitution) -- (τ,leftInv)
  )

data UnificationResult' a
  = Unifies  a                        -- ^ Unification succeeded.
  | NoUnify  NegativeUnification      -- ^ Terms are not unifiable.
  | UnifyBlocked Blocker              -- ^ Unification got blocked on a metavariable
  | UnifyStuck   [UnificationFailure] -- ^ Some other error happened, unification got stuck.
  deriving (Show, Functor, Foldable, Traversable)

-- | Unify indices.
--
--   In @unifyIndices gamma flex a us vs@,
--
--   * @us@ and @vs@ are the argument lists to unify, eliminating type @a@.
--
--   * @gamma@ is the telescope of free variables in @us@ and @vs@.
--
--   * @flex@ is the set of flexible (instantiable) variabes in @us@ and @vs@.
--
--   The result is the most general unifier of @us@ and @vs@.
unifyIndices
  :: (PureTCM m, MonadBench m, BenchPhase m ~ Bench.Phase, MonadError TCErr m)
  => Maybe NoLeftInv -- ^ Do we have a reason for not computing a left inverse?
  -> Telescope       -- ^ @gamma@
  -> FlexibleVars    -- ^ @flex@
  -> Type            -- ^ @a@
  -> Args            -- ^ @us@
  -> Args            -- ^ @vs@
  -> m UnificationResult
unifyIndices linv tel flex a us vs =
  Bench.billTo [Bench.Typing, Bench.CheckLHS, Bench.UnifyIndices] $
    fmap (\(a,b,c,_) -> (a,b,c)) <$> unifyIndices' linv tel flex a us vs

unifyIndices'
  :: (PureTCM m, MonadError TCErr m)
  => Maybe NoLeftInv -- ^ Do we have a reason for not computing a left inverse?
  -> Telescope     -- ^ @gamma@
  -> FlexibleVars  -- ^ @flex@
  -> Type          -- ^ @a@
  -> Args          -- ^ @us@
  -> Args          -- ^ @vs@
  -> m FullUnificationResult
unifyIndices' linv tel flex a [] [] = return $ Unifies (tel, idS, [], Right (idS, raiseS 1))
unifyIndices' linv tel flex a us vs = do
    reportSDoc "tc.lhs.unify" 10 $
      sep [ "unifyIndices"
          , ("tel  =" <+>) $ nest 2 $ prettyTCM tel
          , ("flex =" <+>) $ nest 2 $ addContext tel $ text $ show $ map flexVar flex
          , ("a    =" <+>) $ nest 2 $ addContext tel $ parens (prettyTCM a)
          , ("us   =" <+>) $ nest 2 $ addContext tel $ prettyList $ map prettyTCM us
          , ("vs   =" <+>) $ nest 2 $ addContext tel $ prettyList $ map prettyTCM vs
          ]
    initialState    <- initUnifyState tel flex a us vs
    reportSDoc "tc.lhs.unify" 20 $ "initial unifyState:" <+> prettyTCM initialState
    (result,log) <- runUnifyLogT $ unify initialState rightToLeftStrategy
    forM result $ \ s -> do -- Unifies case
        let output = mconcat [output | (UnificationStep _ _ output,_) <- log ]
        let ps = applySubst (unifyProof output) $ teleNamedArgs (eqTel initialState)
        tauInv <- do
          strict     <- asksTC envSplitOnStrict
          cubicalCompatible <- cubicalCompatibleOption
          withoutK <- withoutKOption
          case linv of
            Just reason -> pure (Left reason)
            Nothing
              | strict            -> pure (Left SplitOnStrict)
              | cubicalCompatible -> buildLeftInverse initialState log
              | withoutK          -> pure (Left NoCubical)
              | otherwise         -> pure (Left WithKEnabled)
        reportSDoc "tc.lhs.unify" 20 $ "ps:" <+> pretty ps
        return $ (varTel s, unifySubst output, ps, tauInv)



type UnifyStrategy = forall m. (PureTCM m, MonadPlus m) => UnifyState -> m UnifyStep


--UNUSED Liang-Ting Chen 2019-07-16
--leftToRightStrategy :: UnifyStrategy
--leftToRightStrategy s =
--    msum (for [0..n-1] $ \k -> completeStrategyAt k s)
--  where n = size $ eqTel s

rightToLeftStrategy :: UnifyStrategy
rightToLeftStrategy s =
    msum (for (downFrom n) $ \k -> completeStrategyAt k s)
  where n = size $ eqTel s

completeStrategyAt :: Int -> UnifyStrategy
completeStrategyAt k s = msum $ map (\strat -> strat k s) $
-- ASR (2021-02-07). The below eta-expansions are required by GHC >=
-- 9.0.1 (see Issue #4955).
    [ (\n -> skipIrrelevantStrategy n)
    , (\n -> basicUnifyStrategy n)
    , (\n -> literalStrategy n)
    , (\n -> dataStrategy n)
    , (\n -> etaExpandVarStrategy  n)
    , (\n -> etaExpandEquationStrategy n)
    , (\n -> injectiveTypeConStrategy n)
    , (\n -> injectivePragmaStrategy n)
    , (\n -> simplifySizesStrategy n)
    , (\n -> checkEqualityStrategy n)
    ]

-- | @isHom n x@ returns x lowered by n if the variables 0..n-1 don't occur in x.
--
-- This is naturally sensitive to normalization.
isHom :: (Free a, Subst a) => Int -> a -> Maybe a
isHom n x = do
  guard $ getAll $ runFree (All . (>= n)) IgnoreNot x
  return $ raise (-n) x

findFlexible :: Int -> FlexibleVars -> Maybe (FlexibleVar Nat)
findFlexible i flex = List.find ((i ==) . flexVar) flex

basicUnifyStrategy :: Int -> UnifyStrategy
basicUnifyStrategy k s = do
  Equal dom@Dom{unDom = a} u v <- eqUnLevel (getEquality k s)
    -- Andreas, 2019-02-23: reduce equality for the sake of isHom?
  ha <- fromMaybeMP $ isHom n a
  (mi, mj) <- addContext (varTel s) $ (,) <$> isEtaVar u ha <*> isEtaVar v ha
  reportSDoc "tc.lhs.unify" 30 $ "isEtaVar results: " <+> text (show [mi,mj])
  case (mi, mj) of
    (Just i, Just j)
     | i == j -> mzero -- Taken care of by checkEqualityStrategy
    (Just i, Just j)
     | Just fi <- findFlexible i flex
     , Just fj <- findFlexible j flex -> do
       let choice = chooseFlex fi fj
           firstTryLeft  = msum [ return (Solution k dom{unDom = ha} fi v left)
                                , return (Solution k dom{unDom = ha} fj u right)]
           firstTryRight = msum [ return (Solution k dom{unDom = ha} fj u right)
                                , return (Solution k dom{unDom = ha} fi v left)]
       reportSDoc "tc.lhs.unify" 40 $ "fi = " <+> text (show fi)
       reportSDoc "tc.lhs.unify" 40 $ "fj = " <+> text (show fj)
       reportSDoc "tc.lhs.unify" 40 $ "chooseFlex: " <+> text (show choice)
       case choice of
         ChooseLeft   -> firstTryLeft
         ChooseRight  -> firstTryRight
         ExpandBoth   -> mzero -- This should be taken care of by etaExpandEquationStrategy
         ChooseEither -> firstTryRight
    (Just i, _)
     | Just fi <- findFlexible i flex -> return $ Solution k dom{unDom = ha} fi v left
    (_, Just j)
     | Just fj <- findFlexible j flex -> return $ Solution k dom{unDom = ha} fj u right
    _ -> mzero
  where
    flex = flexVars s
    n = eqCount s
    left = Left (); right = Right ()

dataStrategy :: Int -> UnifyStrategy
dataStrategy k s = do
  Equal Dom{unDom = a} u v <- eqConstructorForm =<< eqUnLevel =<< getReducedEqualityUnraised k s
  sortOk <- reduce (getSort a) <&> \case
    Type{} -> True
    Inf{}  -> True
    SSet{} -> True
    _      -> False
  case unEl a of
    Def d es | sortOk -> do
      npars <- catMaybesMP $ getNumberOfParameters d
      let (pars,ixs) = splitAt npars $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reportSDoc "tc.lhs.unify" 40 $ addContext (varTel s `abstract` eqTel s) $
        "Found equation at datatype " <+> prettyTCM d
         <+> " with parameters " <+> prettyTCM (raise (size (eqTel s) - k) pars)
      case (u, v) of
        (Con c _ _   , Con c' _ _  ) | c == c' -> return $ Injectivity k a d pars ixs c
        (Con c _ _   , Con c' _ _  ) -> return $ Conflict k a d pars u v
        (Var i []  , v         ) -> ifOccursStronglyRigid i v $ return $ Cycle k a d pars i v
        (u         , Var j []  ) -> ifOccursStronglyRigid j u $ return $ Cycle k a d pars j u
        _ -> mzero
    _ -> mzero
  where
    ifOccursStronglyRigid i u ret = do
        -- Call forceNotFree to reduce u as far as possible
        -- around any occurrences of i
        (_ , u) <- forceNotFree (singleton i) u
        case flexRigOccurrenceIn i u of
          Just StronglyRigid -> ret
          _ -> mzero

checkEqualityStrategy :: Int -> UnifyStrategy
checkEqualityStrategy k s = do
  let Equal Dom{unDom = a} u v = getEquality k s
      n = eqCount s
  ha <- fromMaybeMP $ isHom n a
  return $ Deletion k ha u v

literalStrategy :: Int -> UnifyStrategy
literalStrategy k s = do
  let n = eqCount s
  Equal Dom{unDom = a} u v <- eqUnLevel $ getEquality k s
  ha <- fromMaybeMP $ isHom n a
  (u, v) <- reduce (u, v)
  case (u , v) of
    (Lit l1 , Lit l2)
     | l1 == l2  -> return $ Deletion k ha u v
     | otherwise -> return $ LitConflict k ha l1 l2
    _ -> mzero

etaExpandVarStrategy :: Int -> UnifyStrategy
etaExpandVarStrategy k s = do
  Equal Dom{unDom = a} u v <- eqUnLevel =<< getReducedEquality k s
  shouldEtaExpand u v a s `mplus` shouldEtaExpand v u a s
  where
    -- TODO: use IsEtaVar to check if the term is a variable
    shouldEtaExpand :: Term -> Term -> Type -> UnifyStrategy
    shouldEtaExpand (Var i es) v a s = do
      fi       <- fromMaybeMP $ findFlexible i (flexVars s)
      reportSDoc "tc.lhs.unify" 50 $
        "Found flexible variable " <+> text (show i)
      -- Issue 2888: Do this if there are only projections or if it's a singleton
      -- record or if it's unified against a record constructor term. Basically
      -- we need to avoid EtaExpandEquation if EtaExpandVar is possible, or the
      -- forcing translation is unhappy.
      let k  = varCount s - 1 - i -- position of var i in telescope
          b0 = unDom $ getVarTypeUnraised k s
      b         <- addContext (telFromList $ take k $ telToList $ varTel s) $ reduce b0
      (d, pars) <- catMaybesMP $ isEtaRecordType b
      ps        <- fromMaybeMP $ allProjElims es
      guard =<< orM
        [ pure $ not $ null ps
        , isRecCon v  -- is the other term a record constructor?
        , (Right True ==) <$> runBlocked (isSingletonRecord d pars)
        ]
      reportSDoc "tc.lhs.unify" 50 $
        "with projections " <+> prettyTCM (map snd ps)
      reportSDoc "tc.lhs.unify" 50 $
        "at record type " <+> prettyTCM d
      return $ EtaExpandVar fi d pars
    shouldEtaExpand _ _ _ _ = mzero

    isRecCon (Con c _ _) = isJust <$> isRecordConstructor (conName c)
    isRecCon _           = return False

etaExpandEquationStrategy :: Int -> UnifyStrategy
etaExpandEquationStrategy k s = do
  -- Andreas, 2019-02-23, re #3578, is the following reduce redundant?
  Equal Dom{unDom = a} u v <- getReducedEqualityUnraised k s
  (d, pars) <- catMaybesMP $ addContext tel $ isEtaRecordType a
  guard =<< orM
    [ (Right True ==) <$> runBlocked (isSingletonRecord d pars)
    , shouldProject u
    , shouldProject v
    ]
  return $ EtaExpandEquation k d pars
  where
    shouldProject :: PureTCM m => Term -> m Bool
    shouldProject = \case
      Def f es   -> usesCopatterns f
      Con c _ _  -> isJust <$> isRecordConstructor (conName c)

      Var _ _    -> return False
      Lam _ _    -> __IMPOSSIBLE__
      Lit _      -> __IMPOSSIBLE__
      Pi _ _     -> __IMPOSSIBLE__
      Sort _     -> __IMPOSSIBLE__
      Level _    -> __IMPOSSIBLE__
      MetaV _ _  -> return False
      DontCare _ -> return False
      Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

    tel = varTel s `abstract` telFromList (take k $ telToList $ eqTel s)

simplifySizesStrategy :: Int -> UnifyStrategy
simplifySizesStrategy k s = do
  isSizeName <- isSizeNameTest
  Equal Dom{unDom = a} u v <- getReducedEquality k s
  case unEl a of
    Def d _ -> do
      guard $ isSizeName d
      su <- sizeView u
      sv <- sizeView v
      case (su, sv) of
        (SizeSuc u, SizeSuc v) -> return $ StripSizeSuc k u v
        (SizeSuc u, SizeInf  ) -> return $ StripSizeSuc k u v
        (SizeInf  , SizeSuc v) -> return $ StripSizeSuc k u v
        _ -> mzero
    _ -> mzero

injectiveTypeConStrategy :: Int -> UnifyStrategy
injectiveTypeConStrategy k s = do
  injTyCon <- optInjectiveTypeConstructors <$> pragmaOptions
  guard injTyCon
  eq <- eqUnLevel =<< getReducedEquality k s
  case eq of
    Equal a u@(Def d es) v@(Def d' es') | d == d' -> do
      -- d must be a data, record or axiom
      def <- getConstInfo d
      guard $ case theDef def of
                Datatype{} -> True
                Record{}   -> True
                Axiom{}    -> True
                DataOrRecSig{} -> True
                AbstractDefn{} -> False -- True triggers issue #2250
                Function{}   -> False
                Primitive{}  -> False
                PrimitiveSort{} -> __IMPOSSIBLE__
                GeneralizableVar{} -> __IMPOSSIBLE__
                Constructor{} -> __IMPOSSIBLE__  -- Never a type!
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

injectivePragmaStrategy :: Int -> UnifyStrategy
injectivePragmaStrategy k s = do
  eq <- eqUnLevel =<< getReducedEquality k s
  case eq of
    Equal a u@(Def d es) v@(Def d' es') | d == d' -> do
      -- d must have an injective pragma
      def <- getConstInfo d
      guard $ defInjective def
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

skipIrrelevantStrategy :: Int -> UnifyStrategy
skipIrrelevantStrategy k s = do
  let Equal a _ _ = getEquality k s                                 -- reduce not necessary
  addContext (varTel s `abstract` eqTel s) $
    guard . (== Right True) =<< runBlocked (isIrrelevantOrPropM a)  -- reduction takes place here
  -- TODO: do something in case the above is blocked (i.e. `Left b`)
  return $ SkipIrrelevantEquation k


----------------------------------------------------
-- Actually doing the unification
----------------------------------------------------

unifyStep
  :: (PureTCM m, MonadWriter UnifyOutput m, MonadError TCErr m)
  => UnifyState -> UnifyStep -> m (UnificationResult' UnifyState)
unifyStep s Deletion{ deleteAt = k , deleteType = a , deleteLeft = u , deleteRight = v } = do
    -- Check definitional equality of u and v
    isReflexive <- addContext (varTel s) $ runBlocked $ pureEqualTerm a u v
    withoutK <- withoutKOption
    splitOnStrict <- asksTC envSplitOnStrict
    case isReflexive of
      Left block   -> return $ UnifyBlocked block
      Right False  -> return $ UnifyStuck []
      Right True | withoutK && not splitOnStrict
                   -> return $ UnifyStuck [UnifyReflexiveEq (varTel s) a u]
      Right True   -> do
        let (s', sigma) = solveEq k u s
        tellUnifyProof sigma
        Unifies <$> lensEqTel reduce s'

unifyStep s step@Solution{} = solutionStep RetryNormalised s step

unifyStep s (Injectivity k a d pars ixs c) = do
  ifM (consOfHIT $ conName c) (return $ UnifyStuck []) $ do
  withoutK <- withoutKOption

  -- Split equation telescope into parts before and after current equation
  let (eqListTel1, _ : eqListTel2) = splitAt k $ telToList $ eqTel s
      (eqTel1, eqTel2) = (telFromList eqListTel1, telFromList eqListTel2)

  -- Get constructor telescope and target indices
  cdef  <- getConInfo c
  let ctype  = defType cdef `piApply` pars
  addContext (varTel s `abstract` eqTel1) $ reportSDoc "tc.lhs.unify" 40 $
    "Constructor type: " <+> prettyTCM ctype
  TelV ctel ctarget <- addContext (varTel s `abstract` eqTel1) $ telView ctype
  let cixs = case unEl ctarget of
               Def d' es | d == d' ->
                 let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                 in  drop (length pars) args
               _ -> __IMPOSSIBLE__

  -- Get index telescope of the datatype
  dtype    <- (`piApply` pars) . defType <$> getConstInfo d
  addContext (varTel s `abstract` eqTel1) $ reportSDoc "tc.lhs.unify" 40 $
    "Datatype type: " <+> prettyTCM dtype

  -- This is where the magic of higher-dimensional unification happens
  -- We need to generalize the indices `ixs` to the target indices of the
  -- constructor `cixs`. This is done by calling the unification algorithm
  -- recursively (this doesn't get stuck in a loop because a type should
  -- never be indexed over itself). Note the similarity with the
  -- computeNeighbourhood function in Agda.TypeChecking.Coverage.
  let hduTel = eqTel1 `abstract` ctel
      notforced = replicate (size hduTel) NotForced

  -- The left inverse computed here is not actually used when computing
  -- a left inverse for the overall match, so as a slight optimisation
  -- we just don't bother computing it. __IMPOSSIBLE__ because that
  -- field in the result is never evaluated.
  res <- addContext (varTel s) $ unifyIndices' (Just __IMPOSSIBLE__)
           hduTel
           (allFlexVars notforced hduTel)
           (raise (size ctel) dtype)
           (raise (size ctel) ixs)
           cixs
  case res of
    -- Higher-dimensional unification can never end in a conflict,
    -- because `cong c1 ...` and `cong c2 ...` don't even have the
    -- same type for distinct constructors c1 and c2.
    NoUnify _ -> __IMPOSSIBLE__

    -- Higher-dimensional unification is blocked: propagate
    UnifyBlocked block -> return $ UnifyBlocked block

    -- Higher-dimensional unification has failed. If not --without-K,
    -- we can simply ignore the higher-dimensional equations and
    -- simplify the equation as in the non-indexed case.
    UnifyStuck _ | not withoutK -> do
      -- using the same variable names as in the case where hdu succeeds.
      let eqTel1' = eqTel1 `abstract` ctel
          rho1    = raiseS (size ctel)
          ceq     = ConP c noConPatternInfo $ teleNamedArgs ctel
          rho3    = consS ceq rho1
          eqTel2' = applyPatSubst rho3 eqTel2
          eqTel'  = eqTel1' `abstract` eqTel2'
          rho     = liftS (size eqTel2) rho3

      tellUnifyProof rho

      eqTel' <- addContext (varTel s) $ reduce eqTel'

      -- Compute new lhs and rhs by matching the old ones against rho
      (lhs', rhs') <- addContext (varTel s) $ do
        let ps = applySubst rho $ teleNamedArgs $ eqTel s
        (lhsMatch, _) <- Match.matchPatterns ps $ eqLHS s
        (rhsMatch, _) <- Match.matchPatterns ps $ eqRHS s
        case (lhsMatch, rhsMatch) of
          (Match.Yes _ lhs', Match.Yes _ rhs') -> return
            (reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') lhs',
             reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') rhs')
          _ -> __IMPOSSIBLE__

      return $ Unifies $ s { eqTel = eqTel' , eqLHS = lhs' , eqRHS = rhs' }


    UnifyStuck _ -> let n           = eqCount s
                        Equal Dom{unDom = a} u v = getEquality k s
                    in return $ UnifyStuck [UnifyIndicesNotVars
                         (varTel s `abstract` eqTel s) a
                         (raise n u) (raise n v) (raise (n-k) ixs)]

    Unifies (eqTel1', rho0, _, _) -> do
      -- Split ps0 into parts for eqTel1 and ctel
      let (rho1, rho2) = splitS (size ctel) rho0

      -- Compute new equation telescope context and substitution
      let ceq     = ConP c noConPatternInfo $ applySubst rho2 $ teleNamedArgs ctel
          rho3    = consS ceq rho1
          eqTel2' = applyPatSubst rho3 eqTel2
          eqTel'  = eqTel1' `abstract` eqTel2'
          rho     = liftS (size eqTel2) rho3

      tellUnifyProof rho

      eqTel' <- addContext (varTel s) $ reduce eqTel'

      -- Compute new lhs and rhs by matching the old ones against rho
      (lhs', rhs') <- addContext (varTel s) $ do
        let ps = applySubst rho $ teleNamedArgs $ eqTel s
        (lhsMatch, _) <- Match.matchPatterns ps $ eqLHS s
        (rhsMatch, _) <- Match.matchPatterns ps $ eqRHS s
        case (lhsMatch, rhsMatch) of
          (Match.Yes _ lhs', Match.Yes _ rhs') -> return
            (reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') lhs',
             reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') rhs')
          _ -> __IMPOSSIBLE__

      return $ Unifies $ s { eqTel = eqTel' , eqLHS = lhs' , eqRHS = rhs' }

unifyStep s Conflict
  { conflictLeft  = u
  , conflictRight = v
  } =
  case u of
    Con h _ _ -> do
      ifM (consOfHIT $ conName h) (return $ UnifyStuck []) $ do
        return $ NoUnify $ UnifyConflict (varTel s) u v
    _ -> __IMPOSSIBLE__
unifyStep s Cycle
  { cycleVar        = i
  , cycleOccursIn   = u
  } =
  case u of
    Con h _ _ -> do
      ifM (consOfHIT $ conName h) (return $ UnifyStuck []) $ do
        return $ NoUnify $ UnifyCycle (varTel s) i u
    _ -> __IMPOSSIBLE__

unifyStep s EtaExpandVar{ expandVar = fi, expandVarRecordType = d , expandVarParameters = pars } = do
  recd <- fromMaybe __IMPOSSIBLE__ <$> isRecord d
  let delta = recTel recd `apply` pars
      c     = recConHead recd
  let nfields         = size delta
      (varTel', rho)  = expandTelescopeVar (varTel s) (m-1-i) delta c
      projectFlexible = [ FlexibleVar (getArgInfo fi) (flexForced fi) (projFlexKind j) (flexPos fi) (i+j) | j <- [0..nfields-1] ]
  tellUnifySubst $ rho
  return $ Unifies $ UState
    { varTel   = varTel'
    , flexVars = projectFlexible ++ liftFlexibles nfields (flexVars s)
    , eqTel    = applyPatSubst rho $ eqTel s
    , eqLHS    = applyPatSubst rho $ eqLHS s
    , eqRHS    = applyPatSubst rho $ eqRHS s
    }
  where
    i = flexVar fi
    m = varCount s

    projFlexKind :: Int -> FlexibleVarKind
    projFlexKind j = case flexKind fi of
      RecordFlex ks -> indexWithDefault ImplicitFlex ks j
      ImplicitFlex  -> ImplicitFlex
      DotFlex       -> DotFlex
      OtherFlex     -> OtherFlex

    liftFlexible :: Int -> Int -> Maybe Int
    liftFlexible n j = if j == i then Nothing else Just (if j > i then j + (n-1) else j)

    liftFlexibles :: Int -> FlexibleVars -> FlexibleVars
    liftFlexibles n fs = mapMaybe (traverse $ liftFlexible n) fs

unifyStep s EtaExpandEquation{ expandAt = k, expandRecordType = d, expandParameters = pars } = do
  recd  <- fromMaybe __IMPOSSIBLE__ <$> isRecord d
  let delta = recTel recd `apply` pars
      c     = recConHead recd
  lhs   <- expandKth $ eqLHS s
  rhs   <- expandKth $ eqRHS s
  let (tel, sigma) = expandTelescopeVar (eqTel s) k delta c
  tellUnifyProof sigma
  Unifies <$> do
   lensEqTel reduce $ s
    { eqTel    = tel
    , eqLHS    = lhs
    , eqRHS    = rhs
    }
  where
    expandKth us = do
      let (us1,v:us2) = fromMaybe __IMPOSSIBLE__ $ splitExactlyAt k us
      vs <- snd <$> etaExpandRecord d pars (unArg v)
      vs <- reduce vs
      return $ us1 ++ vs ++ us2

unifyStep s LitConflict
  { litType          = a
  , litConflictLeft  = l
  , litConflictRight = l'
  } = return $ NoUnify $ UnifyConflict (varTel s) (Lit l) (Lit l')

unifyStep s (StripSizeSuc k u v) = do
  sizeTy <- sizeType
  sizeSu <- sizeSuc 1 (var 0)
  let n          = eqCount s
      sub        = liftS (n-k-1) $ consS sizeSu $ raiseS 1
      eqFlatTel  = flattenTel $ eqTel s
      eqFlatTel' = applySubst sub $ updateAt k (fmap $ const sizeTy) $ eqFlatTel
      eqTel'     = unflattenTel (teleNames $ eqTel s) eqFlatTel'
  -- TODO: tellUnifyProof sub
  -- but sizeSu is not a constructor, so sub is not a PatternSubstitution!
  return $ Unifies $ s
    { eqTel = eqTel'
    , eqLHS = updateAt k (const $ defaultArg u) $ eqLHS s
    , eqRHS = updateAt k (const $ defaultArg v) $ eqRHS s
    }

unifyStep s (SkipIrrelevantEquation k) = do
  let lhs = eqLHS s
      (s', sigma) = solveEq k (DontCare $ unArg $ indexWithDefault __IMPOSSIBLE__ lhs k) s
  tellUnifyProof sigma
  return $ Unifies s'

unifyStep s (TypeConInjectivity k d us vs) = do
  dtype <- defType <$> getConstInfo d
  TelV dtel _ <- telView dtype
  let deq = Def d $ map Apply $ teleArgs dtel
  -- TODO: tellUnifyProof ???
  -- but d is not a constructor...
  Unifies <$> do
   lensEqTel reduce $ s
    { eqTel = dtel `abstract` applyUnder k (eqTel s) (raise k deq)
    , eqLHS = us ++ dropAt k (eqLHS s)
    , eqRHS = vs ++ dropAt k (eqRHS s)
    }

data RetryNormalised = RetryNormalised | DontRetryNormalised
  deriving (Eq, Show)

solutionStep
  :: (PureTCM m, MonadWriter UnifyOutput m)
  => RetryNormalised
  -> UnifyState
  -> UnifyStep
  -> m (UnificationResult' UnifyState)
solutionStep retry s
  step@Solution{ solutionAt   = k
               , solutionType = dom@Dom{ unDom = a }
               , solutionVar  = fi@FlexibleVar{ flexVar = i }
               , solutionTerm = u } = do
  let m = varCount s

  -- Now we have to be careful about forced variables in `u`. If they appear
  -- in pattern positions we need to bind them there rather in their forced positions. We can safely
  -- ignore non-pattern positions and forced pattern positions, because in that case there will be
  -- other equations where the variable can be bound.
  -- NOTE: If we're doing make-case we ignore forced variables. This is safe since we take the
  -- result of unification and build user clauses that will be checked again with forcing turned on.
  inMakeCase <- viewTC eMakeCase
  let forcedVars | inMakeCase = IntMap.empty
                 | otherwise  = IntMap.fromList [ (flexVar fi, getModality fi) | fi <- flexVars s,
                                                                                 flexForced fi == Forced ]
  (p, bound) <- patternBindingForcedVars forcedVars u

  -- To maintain the invariant that each variable in varTel is bound exactly once in the pattern
  -- substitution we need to turn the bound variables in `p` into dot patterns in the rest of the
  -- substitution.
  let dotSub = foldr composeS idS [ inplaceS i (dotP (Var i [])) | i <- IntMap.keys bound ]

  -- We moved the binding site of some forced variables, so we need to update their modalities in
  -- the telescope. The new modality is the combination of the modality of the variable we are
  -- instantiating and the modality of the binding site in the pattern (returned by
  -- patternBindingForcedVars).
  let updModality md vars tel
        | IntMap.null vars = tel
        | otherwise        = telFromList $ zipWith upd (downFrom $ size tel) (telToList tel)
        where
          upd i a | Just md' <- IntMap.lookup i vars = setModality (composeModality md md') a
                  | otherwise                        = a
  s <- return $ s { varTel = updModality (getModality fi) bound (varTel s) }

  reportSDoc "tc.lhs.unify.force" 45 $ vcat
    [ "forcedVars =" <+> pretty (IntMap.keys forcedVars)
    , "u          =" <+> prettyTCM u
    , "p          =" <+> prettyTCM p
    , "bound      =" <+> pretty (IntMap.keys bound)
    , "dotSub     =" <+> pretty dotSub ]

  -- Check that the type of the variable is equal to the type of the equation
  -- (not just a subtype), otherwise we cannot instantiate (see Issue 2407).
  let dom'@Dom{ unDom = a' } = getVarType (m-1-i) s
  equalTypes <- addContext (varTel s) $ runBlocked $ do
    reportSDoc "tc.lhs.unify" 45 $ "Equation type: " <+> prettyTCM a
    reportSDoc "tc.lhs.unify" 45 $ "Variable type: " <+> prettyTCM a'
    pureEqualType a a'

  -- The conditions on the relevances are as follows (see #2640):
  -- - If the type of the equation is relevant, then the solution must be
  --   usable in a relevant position.
  -- - If the type of the equation is (shape-)irrelevant, then the solution
  --   must be usable in a μ-relevant position where μ is the relevance
  --   of the variable being solved.
  --
  -- Jesper, Andreas, 2018-10-17: the quantity of the equation is morally
  -- always @Quantity0@, since the indices of the data type are runtime erased.
  -- Thus, we need not change the quantity of the solution.
  envmod <- currentModality
  let eqrel  = getRelevance dom
      eqmod  = getModality dom
      varmod = getModality dom'
      mod    = applyUnless (NonStrict `moreRelevant` eqrel) (setRelevance eqrel)
             $ applyUnless (usableQuantity envmod) (setQuantity zeroQuantity)
             $ varmod
  reportSDoc "tc.lhs.unify" 65 $ text $ "Equation modality: " ++ show (getModality dom)
  reportSDoc "tc.lhs.unify" 65 $ text $ "Variable modality: " ++ show varmod
  reportSDoc "tc.lhs.unify" 65 $ text $ "Solution must be usable in a " ++ show mod ++ " position."
  -- Andreas, 2018-10-18
  -- Currently, the modality check has problems with meta-variables created in the type signature,
  -- and thus, in quantity 0, that get into terms using the unifier, and there are checked to be
  -- non-erased, i.e., have quantity ω.
  -- Ulf, 2019-12-13. We still do it though.
  -- Andrea, 2020-10-15: It looks at meta instantiations now.
  eusable <- addContext (varTel s) $ runExceptT $ usableMod mod u
  caseEitherM (return eusable) (return . UnifyBlocked) $ \ usable -> do

  reportSDoc "tc.lhs.unify" 45 $ "Modality ok: " <+> prettyTCM usable
  unless usable $ reportSDoc "tc.lhs.unify" 65 $ "Rejected solution: " <+> prettyTCM u

  -- We need a Flat equality to solve a Flat variable.
  -- This also ought to take care of the need for a usableCohesion check.
  if not (getCohesion eqmod `moreCohesion` getCohesion varmod) then return $ UnifyStuck [] else do

  case equalTypes of
    Left block  -> return $ UnifyBlocked block
    Right False -> return $ UnifyStuck []
    Right True | usable ->
      case solveVar (m - 1 - i) p s of
        Nothing | retry == RetryNormalised -> do
          u <- normalise u
          s <- lensVarTel normalise s
          solutionStep DontRetryNormalised s step{ solutionTerm = u }
        Nothing ->
          return $ UnifyStuck [UnifyRecursiveEq (varTel s) a i u]
        Just (s', sub) -> do
          let rho = sub `composeS` dotSub
          tellUnifySubst rho
          let (s'', sigma) = solveEq k (applyPatSubst rho u) s'
          tellUnifyProof sigma
          return $ Unifies s''
          -- Andreas, 2019-02-23, issue #3578: do not eagerly reduce
          -- Unifies <$> liftTCM (reduce s'')
    Right True -> return $ UnifyStuck [UnifyUnusableModality (varTel s) a i u mod]
solutionStep _ _ _ = __IMPOSSIBLE__

unify
  :: (PureTCM m, MonadWriter UnifyLog' m, MonadError TCErr m)
  => UnifyState -> UnifyStrategy -> m (UnificationResult' UnifyState)
unify s strategy = if isUnifyStateSolved s
                   then return $ Unifies s
                   else tryUnifyStepsAndContinue (strategy s)
  where
    tryUnifyStepsAndContinue
      :: (PureTCM m, MonadWriter UnifyLog' m, MonadError TCErr m)
      => ListT m UnifyStep -> m (UnificationResult' UnifyState)
    tryUnifyStepsAndContinue steps = do
      x <- foldListT tryUnifyStep failure steps
      case x of
        Unifies s'     -> unify s' strategy
        NoUnify err    -> return $ NoUnify err
        UnifyBlocked b -> return $ UnifyBlocked b
        UnifyStuck err -> return $ UnifyStuck err

    tryUnifyStep :: (PureTCM m, MonadWriter UnifyLog' m, MonadError TCErr m)
                 => UnifyStep
                 -> m (UnificationResult' UnifyState)
                 -> m (UnificationResult' UnifyState)
    tryUnifyStep step fallback = do
      addContext (varTel s) $
        reportSDoc "tc.lhs.unify" 20 $ "trying unifyStep" <+> prettyTCM step
      (x, output) <- runWriterT $ unifyStep s step
      case x of
        Unifies s'   -> do
          reportSDoc "tc.lhs.unify" 20 $ "unifyStep successful."
          reportSDoc "tc.lhs.unify" 20 $ "new unifyState:" <+> prettyTCM s'
          -- tell output
          writeUnifyLog $ (UnificationStep s step output,s')
          return x
        NoUnify{}       -> return x
        UnifyBlocked b1 -> do
          y <- fallback
          case y of
            UnifyStuck _    -> return $ UnifyBlocked b1
            UnifyBlocked b2 -> return $ UnifyBlocked $ unblockOnEither b1 b2
            _               -> return y
        UnifyStuck err1 -> do
          y <- fallback
          case y of
            UnifyStuck err2 -> return $ UnifyStuck $ err1 ++ err2
            _               -> return y

    failure :: Monad m => m (UnificationResult' a)
    failure = return $ UnifyStuck []

-- | Turn a term into a pattern while binding as many of the given forced variables as possible (in
--   non-forced positions).
patternBindingForcedVars :: PureTCM m => IntMap Modality -> Term -> m (DeBruijnPattern, IntMap Modality)
patternBindingForcedVars forced v = do
  let v' = precomputeFreeVars_ v
  runWriterT (evalStateT (go unitModality v') forced)
  where
    noForced v = gets $ IntSet.disjoint (precomputedFreeVars v) . IntMap.keysSet

    bind md i = do
      gets (IntMap.lookup i) >>= \case
        Just md' | related md POLE md' -> do
          -- The new binding site must be more relevant (more relevant = smaller).
          -- "The forcing analysis guarantees that there exists such a position."
          -- Really? Andreas, 2021-08-18, issue #5506
          tell   $ IntMap.singleton i md
          modify $ IntMap.delete i
          return $ varP (deBruijnVar i)
        _ -> return $ dotP (Var i [])

    go md v = ifM (noForced v) (return $ dotP v) $ do
      v' <- lift $ lift $ reduce v
      case v' of
        Var i [] -> bind md i  -- we know i is forced
        Con c ci es
          | Just vs <- allApplyElims es -> do
            fs <- defForced <$> getConstInfo (conName c)
            let goArg Forced    v = return $ fmap (unnamed . dotP) v
                goArg NotForced v = fmap unnamed <$> traverse (go $ composeModality md $ getModality v) v
            (ps, bound) <- listen $ zipWithM goArg (fs ++ repeat NotForced) vs
            if IntMap.null bound
              then return $ dotP v  -- bound nothing
              else do
                let cpi = (toConPatternInfo ci) { conPLazy   = True } -- Not setting conPType. Is this a problem?
                return $ ConP c cpi $ map (setOrigin Inserted) ps
          | otherwise -> return $ dotP v   -- Higher constructor (es has IApply)

        -- Non-pattern positions
        Var _ (_:_) -> return $ dotP v
        Lam{}       -> return $ dotP v
        Pi{}        -> return $ dotP v
        Def{}       -> return $ dotP v
        MetaV{}     -> return $ dotP v
        Sort{}      -> return $ dotP v
        Level{}     -> return $ dotP v
        DontCare{}  -> return $ dotP v
        Dummy{}     -> return $ dotP v
        Lit{}       -> __IMPOSSIBLE__
