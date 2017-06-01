{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NondecreasingIndentation   #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

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
--   1. A telescope @varTel@ of free variables, some or all of which are
--      flexible (as indicated by @flexVars@).
--   2. A telescope @eqTel@ containing the types of the equations.
--   3. Left- and right-hand sides for each equation:
--      @varTel ⊢ eqLHS : eqTel@ and @varTel ⊢ eqRHS : eqTel@.
--
--   The unification algorithm can end in three different ways:
--   (type @UnificationResult@):
--   - A *positive success* @Unifies (tel, sigma, ps)@ with @tel ⊢ sigma : varTel@,
--     @tel ⊢ eqLHS [ varTel ↦ sigma ] ≡ eqRHS [ varTel ↦ sigma ] : eqTel@,
--     and @tel ⊢ ps : eqTel@. In this case, @sigma;ps@ is an *equivalence*
--     between the telescopes @tel@ and @varTel(eqLHS ≡ eqRHS)@.
--   - A *negative success* @NoUnify err@ means that a conflicting equation
--     was found (e.g an equation between two distinct constructors or a cycle).
--   - A *failure* @DontKnow err@ means that the unifier got stuck.
--
--   The unification algorithm itself consists of two parts:
--   1. A *unification strategy* takes a unification problem and produces a
--      list of suggested unification rules (of type @UnifyStep@). Strategies
--      can be constructed by composing simpler strategies (see for example the
--      definition of @completeStrategyAt@).
--   2. The *unification engine* @unifyStep@ takes a unification rule and tries
--      to apply it to the given state, writing the result to the UnifyOutput
--      on a success.
--
--   The unification steps (of type @UnifyStep@) are the following:
--   - *Deletion* removes a reflexive equation @u =?= v : a@ if the left- and
--     right-hand side @u@ and @v@ are (definitionally) equal. This rule results
--     in a failure if --without-K is enabled (see \"Pattern Matching Without K\"
--     by Jesper Cockx, Dominique Devriese, and Frank Piessens (ICFP 2014).
--   - *Solution* solves an equation if one side is (eta-equivalent to) a
--     flexible variable. In case both sides are flexible variables, the
--     unification strategy makes a choice according to the @chooseFlex@
--     function in @Agda.TypeChecking.Rules.LHS.Problem@.
--   - *Injectivity* decomposes an equation of the form
--     @c us =?= c vs : D pars is@ where @c : Δc → D pars js@ is a constructor
--     of the inductive datatype @D@ into a sequence of equations
--     @us =?= vs : delta@. In case @D@ is an indexed datatype,
--     *higher-dimensional unification* is applied (see below).
--   - *Conflict* detects absurd equations of the form
--     @c₁ us =?= c₂ vs : D pars is@ where @c₁@ and @c₂@ are two distinct
--     constructors of the datatype @D@.
--   - *Cycle* detects absurd equations of the form @x =?= v : D pars is@ where
--     @x@ is a variable of the datatype @D@ that occurs strongly rigid in @v@.
--   - *EtaExpandVar* eta-expands a single flexible variable @x : R@ where @R@
--     is a (eta-expandable) record type, replacing it by one variable for each
--     field of @R@.
--   - *EtaExpandEquation* eta-expands an equation @u =?= v : R@ where @R@ is a
--     (eta-expandable) record type, replacing it by one equation for each field
--     of @R@. The left- and right-hand sides of these equations are the
--     projections of @u@ and @v@.
--   - *LitConflict* detects absurd equations of the form @l₁ =?= l₂ : A@ where
--     @l₁@ and @l₂@ are distinct literal terms.
--   - *StripSizeSuc* simplifies an equation of the form
--     @sizeSuc x =?= sizeSuc y : Size@ to @x =?= y : Size@.
--   - *SkipIrrelevantEquation@ removes an equation between irrelevant terms.
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
  , unifyIndices ) where

import Prelude hiding (null)

import Control.Arrow ((***))
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Plus
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.Writer (WriterT(..), MonadWriter(..), Monoid(..))

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup hiding (Arg)
import Data.List hiding (null, sort)

import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)
import qualified Data.Traversable as Trav

import Agda.Interaction.Options (optInjectiveTypeConstructors)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Patterns.Match as Match
import Agda.TypeChecking.Pretty hiding ((<>))
import Agda.TypeChecking.SizedTypes (compareSizes)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.MetaVars (assignV, newArgsMetaCtx)
import Agda.TypeChecking.EtaContract
import Agda.Interaction.Options (optInjectiveTypeConstructors, optWithoutK)

import Agda.TypeChecking.Rules.LHS.Problem hiding (Substitution)
-- import Agda.TypeChecking.SyntacticEquality

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Result of 'unifyIndices'.
type UnificationResult = UnificationResult'
  ( Telescope                  -- @tel@
  , PatternSubstitution        -- @sigma@ s.t. @tel ⊢ sigma : varTel@
  , [NamedArg DeBruijnPattern] -- @ps@    s.t. @tel ⊢ ps    : eqTel @
  )

data UnificationResult' a
  = Unifies  a                    -- ^ Unification succeeded.
  | NoUnify  NegativeUnification  -- ^ Terms are not unifiable.
  | DontKnow [UnificationFailure] -- ^ Some other error happened, unification got stuck.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

-- | Unify indices.
--
--   In @unifyIndices gamma flex us vs@,
--
--   @us@ and @vs@ are the argument lists to unify,
--
--   @gamma@ is the telescope of free variables in @us@ and @vs@.
--
--   @flex@ is the set of flexible (instantiable) variabes in @us@ and @vs@.
--
--   The result is the most general unifier of @us@ and @vs@.
unifyIndices :: MonadTCM tcm
             => Telescope
             -> FlexibleVars
             -> Type
             -> Args
             -> Args
             -> tcm UnificationResult
unifyIndices tel flex a [] [] = return $ Unifies (tel, idS, [])
unifyIndices tel flex a us vs = liftTCM $ Bench.billTo [Bench.Typing, Bench.CheckLHS, Bench.UnifyIndices] $ do
    reportSDoc "tc.lhs.unify" 10 $
      sep [ text "unifyIndices"
          , nest 2 $ prettyTCM tel
          , nest 2 $ addContext tel $ text $ show $ map flexVar flex
          , nest 2 $ addContext tel $ parens (prettyTCM a)
          , nest 2 $ addContext tel $ prettyList $ map prettyTCM us
          , nest 2 $ addContext tel $ prettyList $ map prettyTCM vs
          ]
    initialState    <- initUnifyState tel flex a us vs
    reportSDoc "tc.lhs.unify" 20 $ text "initial unifyState:" <+> prettyTCM initialState
    reportSDoc "tc.lhs.unify" 70 $ text "initial unifyState:" <+> text (show initialState)
    (result,output) <- runUnifyM $ unify initialState rightToLeftStrategy
    let ps = applySubst (unifyProof output) $ teleNamedArgs (eqTel initialState)
    return $ fmap (\s -> (varTel s , unifySubst output , ps)) result

----------------------------------------------------
-- Equalities
----------------------------------------------------

data Equality = Equal
  { eqType  :: Type
  , eqLeft  :: Term
  , eqRight :: Term
  }

instance Reduce Equality where
  reduce' (Equal a u v) = Equal <$> reduce' a <*> reduce' u <*> reduce' v

eqConstructorForm :: Equality -> TCM Equality
eqConstructorForm (Equal a u v) = Equal a <$> constructorForm u <*> constructorForm v

eqUnLevel :: Equality -> TCM Equality
eqUnLevel (Equal a u v) = Equal a <$> unLevel u <*> unLevel v
  where
    unLevel (Level l) = reallyUnLevelView l
    unLevel u         = return u

----------------------------------------------------
-- Unify state
----------------------------------------------------

data UnifyState = UState
  { varTel   :: Telescope
  , flexVars :: FlexibleVars
  , eqTel    :: Telescope
  , eqLHS    :: [Arg Term]
  , eqRHS    :: [Arg Term]
  } deriving (Show)

instance Reduce UnifyState where
  reduce' (UState var flex eq lhs rhs) =
    UState <$> reduce' var
           <*> pure flex
           <*> reduce' eq
           <*> reduce' lhs
           <*> reduce' rhs

reduceVarTel :: UnifyState -> TCM UnifyState
reduceVarTel s@UState{ varTel = tel } = do
  tel <- reduce tel
  return $ s { varTel = tel }

reduceEqTel :: UnifyState -> TCM UnifyState
reduceEqTel s@UState{ eqTel = tel } = do
  tel <- reduce tel
  return $ s { eqTel = tel }

instance Normalise UnifyState where
  normalise' (UState var flex eq lhs rhs) =
    UState <$> normalise' var
           <*> pure flex
           <*> normalise' eq
           <*> normalise' lhs
           <*> normalise' rhs

normaliseVarTel :: UnifyState -> TCM UnifyState
normaliseVarTel s@UState{ varTel = tel } = do
  tel <- normalise tel
  return $ s { varTel = tel }

normaliseEqTel :: UnifyState -> TCM UnifyState
normaliseEqTel s@UState{ eqTel = tel } = do
  tel <- normalise tel
  return $ s { eqTel = tel }

instance PrettyTCM UnifyState where
  prettyTCM state = text "UnifyState" $$ nest 2 (vcat $
    [ text "variable tel:  " <+> prettyTCM gamma
    , text "flexible vars: " <+> prettyTCM (map flexVar $ flexVars state)
    , text "equation tel:  " <+> addContext gamma (prettyTCM delta)
    , text "equations:     " <+> addContext gamma (prettyList_ (zipWith prettyEquality (eqLHS state) (eqRHS state)))
    ])
    where
      gamma = varTel state
      delta = eqTel state
      prettyEquality x y = prettyTCM x <+> text "=?=" <+> prettyTCM y

initUnifyState :: Telescope -> FlexibleVars -> Type -> Args -> Args -> TCM UnifyState
initUnifyState tel flex a lhs rhs = do
  let n = size lhs
  unless (n == size rhs) __IMPOSSIBLE__
  TelV eqTel _ <- telView a
  unless (n == size eqTel) __IMPOSSIBLE__
  reduce $ UState tel flex eqTel lhs rhs

isUnifyStateSolved :: UnifyState -> Bool
isUnifyStateSolved = null . eqTel

varCount :: UnifyState -> Int
varCount = size . varTel

-- | Get the type of the i'th variable in the given state
getVarType :: Int -> UnifyState -> Type
getVarType i s = if i < 0 then __IMPOSSIBLE__ else unDom $ (flattenTel $ varTel s) !! i

getVarTypeUnraised :: Int -> UnifyState -> Type
getVarTypeUnraised i s = if i < 0 then __IMPOSSIBLE__ else snd . unDom $ (telToList $ varTel s) !! i

eqCount :: UnifyState -> Int
eqCount = size . eqTel

-- | Get the k'th equality in the given state. The left- and right-hand sides
--   of the equality live in the varTel telescope, and the type of the equality
--   lives in the varTel++eqTel telescope
getEquality :: Int -> UnifyState -> Equality
getEquality k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
  if k < 0 then __IMPOSSIBLE__ else
    Equal (unDom $ (flattenTel eqs) !! k) (unArg $ lhs !! k) (unArg $ rhs !! k)

-- | As getEquality, but with the unraised type
getEqualityUnraised :: Int -> UnifyState -> Equality
getEqualityUnraised k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
  if k < 0 then __IMPOSSIBLE__ else
    Equal (snd . unDom $ (telToList eqs) !! k)
          (unArg $ lhs !! k)
          (unArg $ rhs !! k)

getEqInfo :: Int -> UnifyState -> ArgInfo
getEqInfo k UState { eqTel = eqs } =
  if k < 0 then __IMPOSSIBLE__ else domInfo $ telToList eqs !! k

-- | Add a list of equations to the front of the equation telescope
addEqs :: Telescope -> [Arg Term] -> [Arg Term] -> UnifyState -> UnifyState
addEqs tel us vs s =
  s { eqTel = tel `abstract` eqTel s
    , eqLHS = us ++ eqLHS s
    , eqRHS = vs ++ eqRHS s
    }
  where k = size tel

addEq :: Type -> Arg Term -> Arg Term -> UnifyState -> UnifyState
addEq a u v = addEqs (ExtendTel (defaultDom a) (Abs underscore EmptyTel)) [u] [v]



-- | Instantiate the k'th variable with the given value.
--   Returns Nothing if there is a cycle.
solveVar :: Int -> Term -> UnifyState -> Maybe (UnifyState, PatternSubstitution)
solveVar k u s = case instantiateTelescope (varTel s) k u of
  Nothing -> Nothing
  Just (tel' , sigma , rho) -> Just $ (,sigma) $ UState
      { varTel   = tel'
      , flexVars = permuteFlex (reverseP rho) $ flexVars s
      , eqTel    = applyPatSubst sigma $ eqTel s
      , eqLHS    = applyPatSubst sigma $ eqLHS s
      , eqRHS    = applyPatSubst sigma $ eqRHS s
      }
  where
    permuteFlex :: Permutation -> FlexibleVars -> FlexibleVars
    permuteFlex perm =
      mapMaybe $ \(FlexibleVar h o k p x) ->
        FlexibleVar h o k p <$> findIndex (x==) (permPicks perm)

applyUnder :: Int -> Telescope -> Term -> Telescope
applyUnder k tel u
 | k < 0     = __IMPOSSIBLE__
 | k == 0    = tel `apply1` u
 | otherwise = case tel of
    EmptyTel         -> __IMPOSSIBLE__
    ExtendTel a tel' -> ExtendTel a $
      Abs (absName tel') $ applyUnder (k-1) (absBody tel') u

dropAt :: Int -> [a] -> [a]
dropAt _ [] = __IMPOSSIBLE__
dropAt k (x:xs)
 | k < 0     = __IMPOSSIBLE__
 | k == 0    = xs
 | otherwise = x : dropAt (k-1) xs

-- | Solve the k'th equation with the given value, which can depend on
--   regular variables but not on other equation variables.
solveEq :: Int -> Term -> UnifyState -> (UnifyState, PatternSubstitution)
solveEq k u s = (,sigma) $ s
    { eqTel    = applyUnder k (eqTel s) u'
    , eqLHS    = dropAt k $ eqLHS s
    , eqRHS    = dropAt k $ eqRHS s
    }
  where
    u'    = raise k u
    n     = eqCount s
    sigma = liftS (n-k-1) $ consS (DotP u') idS

-- | Simplify the k'th equation with the given value (which can depend on other
--   equation variables). Returns Nothing if there is a cycle.
simplifyEq :: Int -> Term -> UnifyState -> Maybe (UnifyState, PatternSubstitution)
simplifyEq k u s = case instantiateTelescope (eqTel s) k u of
  Nothing -> Nothing
  Just (tel' , sigma , rho) -> Just $ (,sigma) $ UState
    { varTel   = varTel s
    , flexVars = flexVars s
    , eqTel    = tel'
    , eqLHS    = permute rho $ eqLHS s
    , eqRHS    = permute rho $ eqRHS s
    }

----------------------------------------------------
-- Unification strategies
----------------------------------------------------

data UnifyStep
  = Deletion
    { deleteAt           :: Int
    , deleteType         :: Type
    , deleteLeft         :: Term
    , deleteRight        :: Term
    }
  | Solution
    { solutionAt         :: Int
    , solutionType       :: Type
    , solutionVar        :: Int
    , solutionTerm       :: Term
    }
  | Injectivity
    { injectAt           :: Int
    , injectType         :: Type
    , injectDatatype     :: QName
    , injectParameters   :: Args
    , injectIndices      :: Args
    , injectConstructor  :: ConHead
    }
  | Conflict
    { conflictAt         :: Int
    , conflictDatatype   :: QName
    , conflictParameters :: Args
    , conflictLeft       :: Term
    , conflictRight      :: Term
    }
  | Cycle
    { cycleAt            :: Int
    , cycleDatatype      :: QName
    , cycleParameters    :: Args
    , cycleVar           :: Int
    , cycleOccursIn      :: Term
    }
  | EtaExpandVar
    { expandVar           :: FlexibleVar Int
    , expandVarRecordType :: QName
    , expandVarParameters :: Args
    }
  | EtaExpandEquation
    { expandAt           :: Int
    , expandRecordType   :: QName
    , expandParameters   :: Args
    }
  | LitConflict
    { litConflictAt      :: Int
    , litType            :: Type
    , litConflictLeft    :: Literal
    , litConflictRight   :: Literal
    }
  | StripSizeSuc
    { stripAt            :: Int
    , stripArgLeft       :: Term
    , stripArgRight      :: Term
    }
  | SkipIrrelevantEquation
    { skipIrrelevantAt   :: Int
    }
  | TypeConInjectivity
    { typeConInjectAt    :: Int
    , typeConstructor    :: QName
    , typeConArgsLeft    :: Args
    , typeConArgsRight   :: Args
    } deriving (Show)

instance PrettyTCM UnifyStep where
  prettyTCM step = case step of
    Deletion k a u v -> text "Deletion" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "type:       " <+> text (show a)
      , text "lhs:        " <+> text (show u)
      , text "rhs:        " <+> text (show v)
      ])
    Solution k a i u -> text "Solution" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "type:       " <+> text (show a)
      , text "variable:   " <+> text (show i)
      , text "term:       " <+> text (show u)
      ])
    Injectivity k a d pars ixs c -> text "Injectivity" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "type:       " <+> text (show a)
      , text "datatype:   " <+> text (show d)
      , text "parameters: " <+> text (show pars)
      , text "indices:    " <+> text (show ixs)
      , text "constructor:" <+> text (show c)
      ])
    Conflict k d pars u v -> text "Conflict" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "datatype:   " <+> text (show d)
      , text "parameters: " <+> text (show pars)
      , text "lhs:        " <+> text (show u)
      , text "rhs:        " <+> text (show v)
      ])
    Cycle k d pars i u -> text "Cycle" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "datatype:   " <+> text (show d)
      , text "parameters: " <+> text (show pars)
      , text "variable:   " <+> text (show i)
      , text "term:       " <+> text (show u)
      ])
    EtaExpandVar fi r pars -> text "EtaExpandVar" $$ nest 2 (vcat $
      [ text "variable:   " <+> text (show fi)
      , text "record type:" <+> text (show r)
      , text "parameters: " <+> text (show pars)
      ])
    EtaExpandEquation k r pars -> text "EtaExpandVar" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "record type:" <+> text (show r)
      , text "parameters: " <+> text (show pars)
      ])
    LitConflict k a u v -> text "LitConflict" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "type:       " <+> text (show a)
      , text "lhs:        " <+> text (show u)
      , text "rhs:        " <+> text (show v)
      ])
    StripSizeSuc k u v -> text "StripSizeSuc" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "lhs:        " <+> text (show u)
      , text "rhs:        " <+> text (show v)
      ])
    SkipIrrelevantEquation k -> text "SkipIrrelevantEquation" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      ])
    TypeConInjectivity k d us vs -> text "TypeConInjectivity" $$ nest 2 (vcat $
      [ text "position:   " <+> text (show k)
      , text "datatype:   " <+> text (show d)
      , text "lhs:        " <+> text (show us)
      , text "rhs:        " <+> text (show vs)
      ])

type UnifyStrategy = UnifyState -> ListT TCM UnifyStep

leftToRightStrategy :: UnifyStrategy
leftToRightStrategy s =
    msum (for [0..n-1] $ \k -> completeStrategyAt k s)
  where n = size $ eqTel s

rightToLeftStrategy :: UnifyStrategy
rightToLeftStrategy s =
    msum (for (downFrom n) $ \k -> completeStrategyAt k s)
  where n = size $ eqTel s

completeStrategyAt :: Int -> UnifyStrategy
completeStrategyAt k s = msum $ map (\strat -> strat k s) $
    [ skipIrrelevantStrategy
    , basicUnifyStrategy
    , literalStrategy
    , dataStrategy
    , etaExpandVarStrategy
    , etaExpandEquationStrategy
    , injectiveTypeConStrategy
    , injectivePragmaStrategy
    , simplifySizesStrategy
    , checkEqualityStrategy
    ]

-- | Returns true if the variables 0..k-1 don't occur in x
isHom :: (Free a, Subst Term a) => Int -> a -> Maybe a
isHom n x = do
  guard $ getAll $ runFree (All . (>= n)) IgnoreNot x
  return $ raise (-n) x

-- | Checks whether the given term (of the given type) is beta-eta-equivalent
--   to a variable. Returns just the de Bruijn-index of the variable if it is,
--   or nothing otherwise.
isEtaVar :: Term -> Type -> TCM (Maybe Int)
isEtaVar u a = runMaybeT $ isEtaVarG u a Nothing []
  where
    -- Checks whether the term u (of type a) is beta-eta-equivalent to
    -- `Var i es`, and returns i if it is. If the argument mi is `Just i'`,
    -- then i and i' are also required to be equal (else Nothing is returned).
    isEtaVarG :: Term -> Type -> Maybe Int -> [Elim' Int] -> MaybeT TCM Int
    isEtaVarG u a mi es = do
      (u, a) <- liftTCM $ reduce (u, a)
      liftTCM $ reportSDoc "tc.lhs.unify" 80 $ text "isEtaVarG" <+> nest 2 (sep
        [ text "u  = " <+> text (show u)
        , text "a  = " <+> prettyTCM a
        , text "mi = " <+> text (show mi)
        , text "es = " <+> prettyList (map (text . show) es)
        ])
      case (ignoreSharing u, ignoreSharing $ unEl a) of
        (Var i' es', _) -> do
          guard $ mi == (i' <$ mi)
          b <- liftTCM $ typeOfBV i'
          areEtaVarElims (var i') b es' es
          return i'
        (_, Def d pars) -> do
          guard =<< do liftTCM $ isEtaRecord d
          fs <- liftTCM $ map unArg . recFields . theDef <$> getConstInfo d
          is <- forM fs $ \f -> do
            let o = ProjSystem
            (_, _, fa) <- MaybeT $ projectTyped u a o f
            isEtaVarG (u `applyE` [Proj o f]) fa mi (es ++ [Proj o f])
          case (mi, is) of
            (Just i, _)     -> return i
            (Nothing, [])   -> mzero
            (Nothing, i:is) -> guard (all (==i) is) >> return i
        (_, Pi dom cod) -> addContext dom $ do
          let u'  = raise 1 u `apply` [argFromDom dom $> var 0]
              a'  = absBody cod
              mi' = fmap (+1) mi
              es' = (fmap . fmap) (+1) es ++ [Apply $ argFromDom dom $> 0]
          (-1+) <$> isEtaVarG u' a' mi' es'
        _ -> mzero

    -- `areEtaVarElims u a es es'` checks whether the given elims es (as applied
    -- to the term u of type a) are beta-eta-equal to either projections or
    -- variables with de Bruijn indices given by es'.
    areEtaVarElims :: Term -> Type -> Elims -> [Elim' Int] -> MaybeT TCM ()
    areEtaVarElims u a []    []    = return ()
    areEtaVarElims u a []    (_:_) = mzero
    areEtaVarElims u a (_:_) []    = mzero
    areEtaVarElims u a (Proj o f : es) (Proj _ f' : es') = do
      guard $ f == f'
      a       <- liftTCM $ reduce a
      (_, _, fa) <- MaybeT $ projectTyped u a o f
      areEtaVarElims (u `applyE` [Proj o f]) fa es es'
    -- These two cases can occur only when we're looking at two different
    -- variables (i.e. one of function type and the other of record type) so
    -- it's definitely not the variable we're looking for (or someone is playing
    -- Jedi mind tricks on us)
    areEtaVarElims u a (Proj{} : _ ) (Apply _ : _  ) = mzero
    areEtaVarElims u a (Apply _ : _ ) (Proj{} : _  ) = mzero
    areEtaVarElims u a (Proj{} : _ ) (IApply{} : _  ) = mzero
    areEtaVarElims u a (IApply{} : _ ) (Proj{} : _  ) = mzero
    areEtaVarElims u a (Apply  _ : _ ) (IApply{} : _  ) = mzero
    areEtaVarElims u a (IApply{} : _ ) (Apply  _ : _  ) = mzero
    areEtaVarElims u a (IApply{} : _) (IApply{} : _) = __IMPOSSIBLE__ -- TODO Andrea: not actually impossible, should be done like Apply
    areEtaVarElims u a (Apply v : es) (Apply i : es') = do
      ifNotPiType a (const mzero) $ \dom cod -> do
      _ <- isEtaVarG (unArg v) (unDom dom) (Just $ unArg i) []
      areEtaVarElims (u `apply` [fmap var i]) (cod `absApp` var (unArg i)) es es'

findFlexible :: Int -> FlexibleVars -> Maybe (FlexibleVar Nat)
findFlexible i flex =
  let flex'      = map flexVar flex
      flexible i = i `elem` flex'
  in find ((i ==) . flexVar) flex

basicUnifyStrategy :: Int -> UnifyStrategy
basicUnifyStrategy k s = do
  Equal a u v <- liftTCM $ eqUnLevel (getEquality k s)
  ha <- mfromMaybe $ isHom n a
  (mi, mj) <- liftTCM $ addContext (varTel s) $ (,) <$> isEtaVar u ha <*> isEtaVar v ha
  liftTCM $ reportSDoc "tc.lhs.unify" 30 $ text "isEtaVar results: " <+> text (show [mi,mj])
  case (mi, mj) of
    (Just i, Just j)
     | i == j -> mzero -- Taken care of by checkEqualityStrategy
    (Just i, Just j)
     | Just fi <- findFlexible i flex
     , Just fj <- findFlexible j flex -> do
       let choice = chooseFlex fi fj
           firstTryLeft  = msum [ return (Solution k ha i v)
                                , return (Solution k ha j u)]
           firstTryRight = msum [ return (Solution k ha j u)
                                , return (Solution k ha i v)]
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "fi = " <+> text (show fi)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "fj = " <+> text (show fj)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "chooseFlex: " <+> text (show choice)
       case choice of
         ChooseLeft   -> firstTryLeft
         ChooseRight  -> firstTryRight
         ExpandBoth   -> mzero -- This should be taken care of by etaExpandEquationStrategy
         ChooseEither -> firstTryRight
    (Just i, _)
     | Just _ <- findFlexible i flex -> return $ Solution k ha i v
    (_, Just j)
     | Just _ <- findFlexible j flex -> return $ Solution k ha j u
    _ -> mzero
  where
    flex = flexVars s
    n = eqCount s

dataStrategy :: Int -> UnifyStrategy
dataStrategy k s = do
  Equal a u v <- liftTCM $ eqConstructorForm =<< eqUnLevel (getEqualityUnraised k s)
  case ignoreSharing $ unEl a of
    Def d es -> do
      npars <- mcatMaybes $ liftTCM $ getNumberOfParameters d
      let (pars,ixs) = splitAt npars $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      hpars <- mfromMaybe $ isHom k pars
      liftTCM $ reportSDoc "tc.lhs.unify" 40 $ addContext (varTel s) $
        text "Found equation at datatype " <+> prettyTCM d
         <+> text " with (homogeneous) parameters " <+> prettyTCM hpars
      case (ignoreSharing u, ignoreSharing v) of
        (MetaV m es, Con c ci _   ) -> do
          let lixs = applySubst (parallelS $ map unArg $ take k $ eqLHS s) ixs
          us <- mcatMaybes $ liftTCM $ addContext (varTel s) $ instMetaCon m es d hpars lixs c ci
          return $ Injectivity k a d hpars ixs c
        (Con c ci _   , MetaV m es) -> do
          let rixs = applySubst (parallelS $ map unArg $ take k $ eqRHS s) ixs
          vs <- mcatMaybes $ liftTCM $ addContext (varTel s) $ instMetaCon m es d hpars rixs c ci
          return $ Injectivity k a d hpars ixs c
        (Con c _ _   , Con c' _ _  ) | c == c' -> return $ Injectivity k a d hpars ixs c
        (Con c _ _   , Con c' _ _  ) -> return $ Conflict k d hpars u v
        (Var i []  , v         ) -> ifOccursStronglyRigid i v $ return $ Cycle k d hpars i v
        (u         , Var j []  ) -> ifOccursStronglyRigid j u $ return $ Cycle k d hpars j u
        _ -> mzero
    _ -> mzero
  where
    ifOccursStronglyRigid i u ret = case occurrence i u of
      StronglyRigid -> ret
      NoOccurrence  -> mzero
      _ -> do
        u <- liftTCM $ normalise u
        case occurrence i u of
          StronglyRigid -> ret
          _ -> mzero

    -- Instantiate the meta with a constructor applied to fresh metas
    -- Returns the fresh metas if successful
    instMetaCon :: MetaId -> Elims -> QName -> Args -> Args -> ConHead -> ConInfo -> TCM (Maybe Args)
    instMetaCon m es d pars ixs c ci = do
      caseMaybe (allApplyElims es) (return Nothing) $ \ us -> do
        ifNotM (asks envAssignMetas) (return Nothing) $ {-else-} tryMaybe $ do
          reportSDoc "tc.lhs.unify" 60 $
            text "Trying to instantiate the meta" <+> prettyTCM (MetaV m es) <+>
            text "with the constructor" <+> prettyTCM c <+> text "applied to fresh metas"
          -- The new metas should have the same dependencies as the original meta
          mv <- lookupMeta m

          ctype <- (`piApply` pars) . defType <$> liftTCM (getConstInfo $ conName c)
          reportSDoc "tc.lhs.unify" 80 $ text "Type of constructor: " <+> prettyTCM ctype

          margs <- withMetaInfo' mv $ do
              let perm = mvPermutation mv
              reportSDoc "tc.lhs.unify" 100 $ vcat
                [ text "Permutation of meta: " <+> prettyTCM perm
                ]
              cxt <- instantiateFull =<< getContextTelescope
              reportSDoc "tc.lhs.unify" 100 $ do
                let flat = flattenTel cxt
                let badRen  :: Substitution = renaming __IMPOSSIBLE__ perm
                let goodRen :: Substitution = renaming __IMPOSSIBLE__ $ flipP perm
                vcat
                  [ text "Context of meta: " <+> (inTopContext $ prettyTCM cxt)
                  , text "Flattened:       " <+> prettyTCM flat
                  , text "Flattened (raw): " <+> text (show flat)
                  , text "Bad renaming:    " <+> text (show badRen)
                  , text "Good renaming:   " <+> text (show goodRen)
                  , text "Raw permutation: " <+> prettyTCM (permute perm flat)
                  ]
              let tel = permuteTel perm cxt
              reportSDoc "tc.lhs.unify" 100 $ text "Context tel (for new metas): " <+> prettyTCM tel
              -- important: create the meta in the same environment as the original meta
              newArgsMetaCtx ctype tel perm us
          reportSDoc "tc.lhs.unify" 80 $ text "Generated meta args: " <+> prettyTCM margs

          let conIxs = case unEl (ctype `piApply` margs) of
                         Def d' es | d == d' -> fromMaybe __IMPOSSIBLE__ $
                           allApplyElims $ drop (length pars) es
                         _ -> __IMPOSSIBLE__

          dType <- (`piApply` pars) . defType <$> liftTCM (getConstInfo d)

          reportSDoc "tc.lhs.unify" 90 $ vcat $
            [ text "Making sure that indices of the meta match those of the constructor:"
            , text "Meta indices:       " <+> prettyTCM ixs
            , text "Constructor indices:" <+> prettyTCM conIxs
            ]
          noConstraints $ compareArgs (repeat Invariant) dType (Def d $ map Apply pars) ixs conIxs

          noConstraints $ assignV DirEq m us (Con c ci margs)
          return margs

checkEqualityStrategy :: Int -> UnifyStrategy
checkEqualityStrategy k s = do
  let Equal a u v = getEquality k s
      n = eqCount s
  ha <- mfromMaybe $ isHom n a
  return $ Deletion k ha u v

literalStrategy :: Int -> UnifyStrategy
literalStrategy k s = do
  eq <- liftTCM $ eqUnLevel $ getEquality k s
  case eq of
    Equal a u@(Lit l1) v@(Lit l2)
     | l1 == l2  -> return $ Deletion k a u u -- TODO: wrong context of a, but does it matter?
     | otherwise -> return $ LitConflict k a l1 l2 -- same problem here
    _ -> mzero

etaExpandVarStrategy :: Int -> UnifyStrategy
etaExpandVarStrategy k s = do
  Equal a u v <- liftTCM $ eqUnLevel (getEquality k s)
  shouldEtaExpand u a s `mplus` shouldEtaExpand v a s
  where
    -- TODO: use IsEtaVar to check if the term is a variable
    shouldEtaExpand :: Term -> Type -> UnifyStrategy
    shouldEtaExpand (Var i es) a s = do
      fi       <- mfromMaybe $ findFlexible i (flexVars s)
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        text "Found flexible variable " <+> text (show i)
      ps       <- mfromMaybe $ allProjElims es
      guard $ not $ null ps
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        text "with projections " <+> prettyTCM (map snd ps)
      let b = getVarTypeUnraised (varCount s - 1 - i) s
      (d, pars) <- mcatMaybes $ liftTCM $ isEtaRecordType b
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        text "at record type " <+> prettyTCM d
      return $ EtaExpandVar fi d pars
    shouldEtaExpand _ _ _ = mzero

etaExpandEquationStrategy :: Int -> UnifyStrategy
etaExpandEquationStrategy k s = do
  let Equal a u v = getEqualityUnraised k s
  (d, pars) <- mcatMaybes $ liftTCM $ addContext tel $ isEtaRecordType a
  sing <- liftTCM $ (Right True ==) <$> isSingletonRecord d pars
  projLeft <- liftTCM $ shouldProject u
  projRight <- liftTCM $ shouldProject v
  guard $ sing || projLeft || projRight
  return $ EtaExpandEquation k d pars
  where
    shouldProject :: Term -> TCM Bool
    shouldProject u = case ignoreSharing u of
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
      Shared _   -> __IMPOSSIBLE__

    tel = varTel s `abstract` telFromList (take k $ telToList $ eqTel s)

simplifySizesStrategy :: Int -> UnifyStrategy
simplifySizesStrategy k s = do
  isSizeName <- liftTCM isSizeNameTest
  let Equal a u v = getEquality k s
  case ignoreSharing $ unEl a of
    Def d _ -> do
      guard $ isSizeName d
      su <- liftTCM $ sizeView u
      sv <- liftTCM $ sizeView v
      case (su, sv) of
        (SizeSuc u, SizeSuc v) -> return $ StripSizeSuc k u v
        (SizeSuc u, SizeInf  ) -> return $ StripSizeSuc k u v
        (SizeInf  , SizeSuc v) -> return $ StripSizeSuc k u v
        _ -> mzero
    _ -> mzero

injectiveTypeConStrategy :: Int -> UnifyStrategy
injectiveTypeConStrategy k s = do
  injTyCon <- liftTCM $ optInjectiveTypeConstructors <$> pragmaOptions
  guard injTyCon
  eq <- liftTCM $ eqUnLevel $ getEquality k s
  case eq of
    Equal a u@(ignoreSharing -> Def d es) v@(ignoreSharing -> Def d' es') | d == d' -> do
      -- d must be a data, record or axiom
      def <- liftTCM $ getConstInfo d
      guard $ case theDef def of
                Datatype{} -> True
                Record{}   -> True
                Axiom{}    -> True
                AbstractDefn -> False -- True triggers issue #2250
                Function{}   -> False
                Primitive{}  -> False
                Constructor{}-> __IMPOSSIBLE__  -- Never a type!
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

injectivePragmaStrategy :: Int -> UnifyStrategy
injectivePragmaStrategy k s = do
  eq <- liftTCM $ eqUnLevel $ getEquality k s
  case eq of
    Equal a u@(ignoreSharing -> Def d es) v@(ignoreSharing -> Def d' es') | d == d' -> do
      -- d must have an injective pragma
      def <- liftTCM $ getConstInfo d
      guard $ defInjective def
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

skipIrrelevantStrategy :: Int -> UnifyStrategy
skipIrrelevantStrategy k s = do
  let i = getEqInfo k s
  guard $ isIrrelevant i
  return $ SkipIrrelevantEquation k


----------------------------------------------------
-- Actually doing the unification
----------------------------------------------------

data UnifyLogEntry
  = UnificationDone  UnifyState
  | UnificationStep  UnifyState UnifyStep

type UnifyLog = [UnifyLogEntry]

data UnifyOutput = UnifyOutput
  { unifySubst :: PatternSubstitution
  , unifyProof :: PatternSubstitution
  , unifyLog   :: UnifyLog
  }

instance Semigroup UnifyOutput where
  x <> y = UnifyOutput
    { unifySubst = unifySubst y `composeS` unifySubst x
    , unifyProof = unifyProof y `composeS` unifyProof x
    , unifyLog   = unifyLog x ++ unifyLog y
    }

instance Monoid UnifyOutput where
  mempty  = UnifyOutput IdS IdS []
  mappend = (<>)

type UnifyM a = WriterT UnifyOutput TCM a

tellUnifySubst :: PatternSubstitution -> UnifyM ()
tellUnifySubst sub = tell $ UnifyOutput sub IdS []

tellUnifyProof :: PatternSubstitution -> UnifyM ()
tellUnifyProof sub = tell $ UnifyOutput IdS sub []

writeUnifyLog :: UnifyLogEntry -> UnifyM ()
writeUnifyLog x = tell $ UnifyOutput IdS IdS [x]

runUnifyM :: UnifyM a -> TCM (a,UnifyOutput)
runUnifyM = runWriterT

unifyStep :: UnifyState -> UnifyStep -> UnifyM (UnificationResult' UnifyState)

unifyStep s Deletion{ deleteAt = k , deleteType = a , deleteLeft = u , deleteRight = v } = do
    -- Check definitional equality of u and v
    isReflexive <- liftTCM $ addContext (varTel s) $ do
      dontAssignMetas $ disableDestructiveUpdate $ noConstraints $
        equalTerm a u v
      return Nothing
      `catchError` \err -> return $ Just err
    withoutK <- liftTCM $ optWithoutK <$> pragmaOptions
    case isReflexive of
      Just err     -> return $ DontKnow []
      _ | withoutK -> return $ DontKnow [UnifyReflexiveEq (varTel s) a u]
      _            -> do
        let (s', sigma) = solveEq k u s
        tellUnifyProof sigma
        Unifies <$> liftTCM (reduceEqTel s')

unifyStep s Solution{ solutionAt = k , solutionType = a , solutionVar = i , solutionTerm = u } = do
  let m = varCount s

  -- Check that the type of the variable is equal to the type of the equation
  -- (not just a subtype), otherwise we cannot instantiate (see Issue 2407).
  let a' = getVarType (m-1-i) s
  equalTypes <- liftTCM $ addContext (varTel s) $ do
    reportSDoc "tc.lhs.unify" 45 $ text "Equation type: " <+> prettyTCM a
    reportSDoc "tc.lhs.unify" 45 $ text "Variable type: " <+> prettyTCM a'
    dontAssignMetas $ disableDestructiveUpdate $ noConstraints $
      equalType a a'
    return Nothing
    `catchError` \err -> return $ Just err
  case equalTypes of
    Just err -> return $ DontKnow []
    Nothing  -> caseMaybeM (trySolveVar (m-1-i) u s)
      (return $ DontKnow [UnifyRecursiveEq (varTel s) a i u])
      (\(s',sub) -> do
        tellUnifySubst sub
        let (s'', sigma) = solveEq k (applyPatSubst sub u) s'
        tellUnifyProof sigma
        Unifies <$> liftTCM (reduce s''))
  where
    trySolveVar i u s = case solveVar i u s of
      Just x  -> return $ Just x
      Nothing -> do
        u <- liftTCM $ normalise u
        s <- liftTCM $ normaliseVarTel s
        return $ solveVar i u s

unifyStep s (Injectivity k a d pars ixs c) = do
  withoutK <- liftTCM $ optWithoutK <$> pragmaOptions
  let n = eqCount s

  -- Get constructor telescope and target indices
  ctype <- (`piApply` pars) . defType <$> liftTCM (getConInfo c)
  addContext (varTel s) $ reportSDoc "tc.lhs.unify" 40 $
    text "Constructor type: " <+> prettyTCM ctype
  TelV ctel ctarget <- liftTCM $ telView ctype
  let cixs = case ignoreSharing $ unEl ctarget of
               Def d' es | d == d' ->
                 let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                 in  drop (length pars) args
               _ -> __IMPOSSIBLE__

  -- Get index telescope of the datatype
  dtype    <- (`piApply` pars) . defType <$> liftTCM (getConstInfo d)
  addContext (varTel s) $ reportSDoc "tc.lhs.unify" 40 $
    text "Datatype type: " <+> prettyTCM dtype

  -- Split equation telescope into parts before and after current equation
  let (eqListTel1, _ : eqListTel2) = genericSplitAt k $ telToList $ eqTel s
      (eqTel1, eqTel2) = (telFromList eqListTel1, telFromList eqListTel2)

  -- This is where the magic of higher-dimensional unification happens
  -- We need to generalize the indices `ixs` to the target indices of the
  -- constructor `cixs`. This is done by calling the unification algorithm
  -- recursively (this doesn't get stuck in a loop because a type should
  -- never be indexed over itself). Note the similarity with the
  -- computeNeighbourhood function in Agda.TypeChecking.Coverage.
  let hduTel = eqTel1 `abstract` raise (size eqTel1) ctel
  res <- liftTCM $ addContext (varTel s) $ unifyIndices
           hduTel
           (allFlexVars hduTel)
           (raise (size hduTel) dtype)
           (raise (size ctel) ixs)
           (raiseFrom (size ctel) (size eqTel1) cixs)
  case res of
    -- Higher-dimensional unification can never end in a conflict,
    -- because `cong c1 ...` and `cong c2 ...` don't even have the
    -- same type for distinct constructors c1 and c2.
    NoUnify _ -> __IMPOSSIBLE__

    -- TODO: we could still make progress here if not --without-K,
    -- but I'm not sure if it's necessary.
    DontKnow _ -> let n           = eqCount s
                      Equal a u v = getEquality k s
                  in return $ DontKnow [UnifyIndicesNotVars
                       (varTel s `abstract` eqTel s) a
                       (raise n u) (raise n v) (raise (n-k) ixs)]

    Unifies (eqTel1', rho0, _) -> do
      -- Split ps0 into parts for eqTel1 and ctel
      let (rho1, rho2) = splitS (size ctel) rho0

      -- Compute new equation telescope context and substitution
      let ceq     = ConP c noConPatternInfo $ applySubst rho2 $ teleNamedArgs ctel
          rho3    = consS ceq rho1
          eqTel2' = applyPatSubst rho3 eqTel2
          eqTel'  = eqTel1' `abstract` eqTel2'
          rho     = liftS (size eqTel2) rho3

      tellUnifyProof rho

      eqTel' <- liftTCM $ reduce eqTel'

      -- Compute new lhs and rhs by matching the old ones against rho
      (lhs', rhs') <- liftTCM . reduce =<< do
        let ps = applySubst rho $ teleNamedArgs $ eqTel s
        (lhsMatch, _) <- liftTCM $ runReduceM $ Match.matchPatterns ps $ eqLHS s
        (rhsMatch, _) <- liftTCM $ runReduceM $ Match.matchPatterns ps $ eqRHS s
        case (lhsMatch, rhsMatch) of
          (Match.Yes _ lhs', Match.Yes _ rhs') -> return
            (reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') lhs',
             reverse $ Match.matchedArgs __IMPOSSIBLE__ (size eqTel') rhs')
          _ -> __IMPOSSIBLE__

      return $ Unifies $ s { eqTel = eqTel' , eqLHS = lhs' , eqRHS = rhs' }

unifyStep s Conflict
  { conflictLeft  = u
  , conflictRight = v
  } = return $ NoUnify $ UnifyConflict (varTel s) u v

unifyStep s Cycle
  { cycleVar        = i
  , cycleOccursIn   = u
  } = return $ NoUnify $ UnifyCycle (varTel s) i u

unifyStep s EtaExpandVar{ expandVar = fi, expandVarRecordType = d , expandVarParameters = pars } = do
  delta   <- liftTCM $ (`apply` pars) <$> getRecordFieldTypes d
  c       <- liftTCM $ getRecordConstructor d
  let nfields         = size delta
      (varTel', rho)  = expandTelescopeVar (varTel s) (m-1-i) delta c
      projectFlexible = [ FlexibleVar (flexHiding fi) (flexOrigin fi) (projFlexKind j) (flexPos fi) (i+j) | j <- [0..nfields-1] ]
  tellUnifySubst $ rho
  Unifies <$> liftTCM (reduce $ UState
    { varTel   = varTel'
    , flexVars = projectFlexible ++ liftFlexibles nfields (flexVars s)
    , eqTel    = applyPatSubst rho $ eqTel s
    , eqLHS    = applyPatSubst rho $ eqLHS s
    , eqRHS    = applyPatSubst rho $ eqRHS s
    })
  where
    i = flexVar fi
    m = varCount s
    n = eqCount s

    projFlexKind :: Int -> FlexibleVarKind
    projFlexKind j = case flexKind fi of
      RecordFlex ks -> fromMaybe ImplicitFlex $ ks !!! j
      ImplicitFlex  -> ImplicitFlex
      DotFlex       -> DotFlex

    liftFlexible :: Int -> Int -> Maybe Int
    liftFlexible n j = if j == i then Nothing else Just (if j > i then j + (n-1) else j)

    liftFlexibles :: Int -> FlexibleVars -> FlexibleVars
    liftFlexibles n fs = catMaybes $ map (traverse $ liftFlexible n) fs

unifyStep s EtaExpandEquation{ expandAt = k, expandRecordType = d, expandParameters = pars } = do
  delta <- liftTCM $ (`apply` pars) <$> getRecordFieldTypes d
  c     <- liftTCM $ getRecordConstructor d
  lhs   <- expandKth $ eqLHS s
  rhs   <- expandKth $ eqRHS s
  let (tel, sigma) = expandTelescopeVar (eqTel s) k delta c
  tellUnifyProof sigma
  Unifies <$> liftTCM (reduceEqTel $ s
    { eqTel    = tel
    , eqLHS    = lhs
    , eqRHS    = rhs
    })
  where
    expandKth us = do
      let (us1,v:us2) = fromMaybe __IMPOSSIBLE__ $ splitExactlyAt k us
      vs <- liftTCM $ snd <$> etaExpandRecord d pars (unArg v)
      vs <- liftTCM $ reduce vs
      return $ us1 ++ vs ++ us2

unifyStep s LitConflict
  { litType          = a
  , litConflictLeft  = l
  , litConflictRight = l'
  } = return $ NoUnify $ UnifyConflict (varTel s) (Lit l) (Lit l')

unifyStep s (StripSizeSuc k u v) = do
  sizeTy <- liftTCM sizeType
  sizeSu <- liftTCM $ sizeSuc 1 (var 0)
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
      (s', sigma) = solveEq k (DontCare $ unArg $ lhs !! k) s
  tellUnifyProof sigma
  return $ Unifies s'

unifyStep s (TypeConInjectivity k d us vs) = do
  dtype <- defType <$> liftTCM (getConstInfo d)
  TelV dtel _ <- liftTCM $ telView dtype
  let n   = eqCount s
      m   = size dtel
      deq = Def d $ map Apply $ teleArgs dtel
  -- TODO: tellUnifyProof ???
  -- but d is not a constructor...
  Unifies <$> liftTCM (reduceEqTel $ s
    { eqTel = dtel `abstract` applyUnder k (eqTel s) (raise k deq)
    , eqLHS = us ++ dropAt k (eqLHS s)
    , eqRHS = vs ++ dropAt k (eqRHS s)
    })

unify :: UnifyState -> UnifyStrategy -> UnifyM (UnificationResult' UnifyState)
unify s strategy = if isUnifyStateSolved s
                   then return $ Unifies s
                   else tryUnifyStepsAndContinue (strategy s)
  where
    tryUnifyStepsAndContinue :: ListT TCM UnifyStep -> UnifyM (UnificationResult' UnifyState)
    tryUnifyStepsAndContinue steps = do
      x <- foldListT tryUnifyStep failure $ liftListT lift steps
      case x of
        Unifies s'   -> unify s' strategy
        NoUnify err  -> return $ NoUnify err
        DontKnow err -> return $ DontKnow err

    tryUnifyStep :: UnifyStep
                 -> UnifyM (UnificationResult' UnifyState)
                 -> UnifyM (UnificationResult' UnifyState)
    tryUnifyStep step fallback = do
      reportSDoc "tc.lhs.unify" 20 $ text "trying unifyStep" <+> prettyTCM step
      x <- unifyStep s step
      case x of
        Unifies s'   -> do
          reportSDoc "tc.lhs.unify" 20 $ text "unifyStep successful."
          reportSDoc "tc.lhs.unify" 20 $ text "new unifyState:" <+> prettyTCM s'
          writeUnifyLog $ UnificationStep s step
          return x
        NoUnify{}     -> return x
        DontKnow err1 -> do
          y <- fallback
          case y of
            DontKnow err2 -> return $ DontKnow $ err1 ++ err2
            _             -> return y

    failure :: UnifyM (UnificationResult' a)
    failure = return $ DontKnow []
