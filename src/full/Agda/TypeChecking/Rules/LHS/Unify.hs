{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NondecreasingIndentation   #-}
{-# LANGUAGE UndecidableInstances       #-}

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
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.Writer (WriterT(..), MonadWriter(..), Monoid(..))

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup hiding (Arg)
import qualified Data.List as List

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
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Patterns.Match as Match
import Agda.TypeChecking.Pretty hiding ((<>))
import Agda.TypeChecking.SizedTypes (compareSizes)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.MetaVars (assignV, newArgsMetaCtx)
import Agda.TypeChecking.EtaContract
import Agda.Interaction.Options (optInjectiveTypeConstructors)

import Agda.TypeChecking.Rules.LHS.Problem
-- import Agda.TypeChecking.SyntacticEquality

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Singleton
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
  deriving (Show, Functor, Foldable, Traversable)

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
      sep [ "unifyIndices"
          , nest 2 $ prettyTCM tel
          , nest 2 $ addContext tel $ text $ show $ map flexVar flex
          , nest 2 $ addContext tel $ parens (prettyTCM a)
          , nest 2 $ addContext tel $ prettyList $ map prettyTCM us
          , nest 2 $ addContext tel $ prettyList $ map prettyTCM vs
          ]
    initialState    <- initUnifyState tel flex a us vs
    reportSDoc "tc.lhs.unify" 20 $ "initial unifyState:" <+> prettyTCM initialState
    reportSDoc "tc.lhs.unify" 70 $ "initial unifyState:" <+> text (show initialState)
    (result,output) <- runUnifyM $ unify initialState rightToLeftStrategy
    let ps = applySubst (unifyProof output) $ teleNamedArgs (eqTel initialState)
    return $ fmap (\s -> (varTel s , unifySubst output , ps)) result

----------------------------------------------------
-- Equalities
----------------------------------------------------

data Equality = Equal
  { eqType  :: Dom Type
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
  prettyTCM state = "UnifyState" $$ nest 2 (vcat $
    [ "variable tel:  " <+> prettyTCM gamma
    , "flexible vars: " <+> prettyTCM (map flexVar $ flexVars state)
    , "equation tel:  " <+> addContext gamma (prettyTCM delta)
    , "equations:     " <+> addContext gamma (prettyList_ (zipWith prettyEquality (eqLHS state) (eqRHS state)))
    ])
    where
      gamma = varTel state
      delta = eqTel state
      prettyEquality x y = prettyTCM x <+> "=?=" <+> prettyTCM y

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
getVarType :: Int -> UnifyState -> Dom Type
getVarType i s = indexWithDefault __IMPOSSIBLE__ (flattenTel $ varTel s) i

getVarTypeUnraised :: Int -> UnifyState -> Dom Type
getVarTypeUnraised i s = snd <$> indexWithDefault __IMPOSSIBLE__ (telToList $ varTel s) i

eqCount :: UnifyState -> Int
eqCount = size . eqTel

-- | Get the k'th equality in the given state. The left- and right-hand sides
--   of the equality live in the varTel telescope, and the type of the equality
--   lives in the varTel++eqTel telescope
getEquality :: Int -> UnifyState -> Equality
getEquality k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
    Equal (indexWithDefault __IMPOSSIBLE__ (flattenTel eqs) k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ lhs k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ rhs k)

-- | As getEquality, but with the unraised type
getEqualityUnraised :: Int -> UnifyState -> Equality
getEqualityUnraised k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
    Equal (snd <$> indexWithDefault __IMPOSSIBLE__ (telToList eqs) k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ lhs k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ rhs k)

getEqInfo :: Int -> UnifyState -> ArgInfo
getEqInfo k UState { eqTel = eqs } =
  domInfo $ indexWithDefault __IMPOSSIBLE__ (telToList eqs) k

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
solveVar :: Int    -- ^ Index @k@
         -> Term   -- ^ Solution @u@
         -> UnifyState -> Maybe (UnifyState, PatternSubstitution)
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
        FlexibleVar h o k p <$> List.findIndex (x==) (permPicks perm)

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
    sigma = liftS (n-k-1) $ consS (dotP u') idS

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
    , solutionType       :: Dom Type
    , solutionVar        :: FlexibleVar Int
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
    , conflictType       :: Type
    , conflictDatatype   :: QName
    , conflictParameters :: Args
    , conflictLeft       :: Term
    , conflictRight      :: Term
    }
  | Cycle
    { cycleAt            :: Int
    , cycleType          :: Type
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
    Deletion k a u v -> "Deletion" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "lhs:        " <+> prettyTCM u
      , "rhs:        " <+> prettyTCM v
      ])
    Solution k a i u -> "Solution" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "variable:   " <+> text (show i)
      , "term:       " <+> prettyTCM u
      ])
    Injectivity k a d pars ixs c -> "Injectivity" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "datatype:   " <+> prettyTCM d
      , "parameters: " <+> prettyList_ (map prettyTCM pars)
      , "indices:    " <+> prettyList_ (map prettyTCM ixs)
      , "constructor:" <+> prettyTCM c
      ])
    Conflict k a d pars u v -> "Conflict" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "datatype:   " <+> prettyTCM d
      , "parameters: " <+> prettyList_ (map prettyTCM pars)
      , "lhs:        " <+> prettyTCM u
      , "rhs:        " <+> prettyTCM v
      ])
    Cycle k a d pars i u -> "Cycle" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "datatype:   " <+> prettyTCM d
      , "parameters: " <+> prettyList_ (map prettyTCM pars)
      , "variable:   " <+> text (show i)
      , "term:       " <+> prettyTCM u
      ])
    EtaExpandVar fi r pars -> "EtaExpandVar" $$ nest 2 (vcat $
      [ "variable:   " <+> text (show fi)
      , "record type:" <+> prettyTCM r
      , "parameters: " <+> prettyTCM pars
      ])
    EtaExpandEquation k r pars -> "EtaExpandEquation" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "record type:" <+> prettyTCM r
      , "parameters: " <+> prettyTCM pars
      ])
    LitConflict k a u v -> "LitConflict" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "lhs:        " <+> prettyTCM u
      , "rhs:        " <+> prettyTCM v
      ])
    StripSizeSuc k u v -> "StripSizeSuc" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "lhs:        " <+> prettyTCM u
      , "rhs:        " <+> prettyTCM v
      ])
    SkipIrrelevantEquation k -> "SkipIrrelevantEquation" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      ])
    TypeConInjectivity k d us vs -> "TypeConInjectivity" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "datatype:   " <+> prettyTCM d
      , "lhs:        " <+> prettyList_ (map prettyTCM us)
      , "rhs:        " <+> prettyList_ (map prettyTCM vs)
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

findFlexible :: Int -> FlexibleVars -> Maybe (FlexibleVar Nat)
findFlexible i flex =
  let flex'      = map flexVar flex
      flexible i = i `elem` flex'
  in List.find ((i ==) . flexVar) flex

basicUnifyStrategy :: Int -> UnifyStrategy
basicUnifyStrategy k s = do
  Equal dom@Dom{unDom = a} u v <- liftTCM $ eqUnLevel (getEquality k s)
  ha <- fromMaybeMP $ isHom n a
  (mi, mj) <- liftTCM $ addContext (varTel s) $ (,) <$> isEtaVar u ha <*> isEtaVar v ha
  liftTCM $ reportSDoc "tc.lhs.unify" 30 $ "isEtaVar results: " <+> text (show [mi,mj])
  case (mi, mj) of
    (Just i, Just j)
     | i == j -> mzero -- Taken care of by checkEqualityStrategy
    (Just i, Just j)
     | Just fi <- findFlexible i flex
     , Just fj <- findFlexible j flex -> do
       let choice = chooseFlex fi fj
           firstTryLeft  = msum [ return (Solution k dom{unDom = ha} fi v)
                                , return (Solution k dom{unDom = ha} fj u)]
           firstTryRight = msum [ return (Solution k dom{unDom = ha} fj u)
                                , return (Solution k dom{unDom = ha} fi v)]
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ "fi = " <+> text (show fi)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ "fj = " <+> text (show fj)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ "chooseFlex: " <+> text (show choice)
       case choice of
         ChooseLeft   -> firstTryLeft
         ChooseRight  -> firstTryRight
         ExpandBoth   -> mzero -- This should be taken care of by etaExpandEquationStrategy
         ChooseEither -> firstTryRight
    (Just i, _)
     | Just fi <- findFlexible i flex -> return $ Solution k dom{unDom = ha} fi v
    (_, Just j)
     | Just fj <- findFlexible j flex -> return $ Solution k dom{unDom = ha} fj u
    _ -> mzero
  where
    flex = flexVars s
    n = eqCount s

dataStrategy :: Int -> UnifyStrategy
dataStrategy k s = do
  Equal Dom{unDom = a} u v <- liftTCM $ eqConstructorForm =<< eqUnLevel (getEqualityUnraised k s)
  case unEl a of
    Def d es | Type{} <- getSort a -> do
      npars <- catMaybesMP $ liftTCM $ getNumberOfParameters d
      let (pars,ixs) = splitAt npars $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      hpars <- fromMaybeMP $ isHom k pars
      liftTCM $ reportSDoc "tc.lhs.unify" 40 $ addContext (varTel s) $
        "Found equation at datatype " <+> prettyTCM d
         <+> " with (homogeneous) parameters " <+> prettyTCM hpars
      case (u, v) of
        (Con c _ _   , Con c' _ _  ) | c == c' -> return $ Injectivity k a d hpars ixs c
        (Con c _ _   , Con c' _ _  ) -> return $ Conflict k a d hpars u v
        (Var i []  , v         ) -> ifOccursStronglyRigid i v $ return $ Cycle k a d hpars i v
        (u         , Var j []  ) -> ifOccursStronglyRigid j u $ return $ Cycle k a d hpars j u
        _ -> mzero
    _ -> mzero
  where
    ifOccursStronglyRigid i u ret = do
        -- Call forceNotFree to reduce u as far as possible
        -- around any occurrences of i
        (_ , u) <- liftTCM $ forceNotFree (singleton i) u
        case occurrence i u of
          StronglyRigid -> ret
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
  Equal Dom{unDom = a} u v <- liftTCM $ eqUnLevel $ getEquality k s
  ha <- fromMaybeMP $ isHom n a
  case (u , v) of
    (Lit l1 , Lit l2)
     | l1 == l2  -> return $ Deletion k ha u v
     | otherwise -> return $ LitConflict k ha l1 l2
    _ -> mzero

etaExpandVarStrategy :: Int -> UnifyStrategy
etaExpandVarStrategy k s = do
  Equal Dom{unDom = a} u v <- liftTCM $ eqUnLevel (getEquality k s)
  shouldEtaExpand u v a s `mplus` shouldEtaExpand v u a s
  where
    -- TODO: use IsEtaVar to check if the term is a variable
    shouldEtaExpand :: Term -> Term -> Type -> UnifyStrategy
    shouldEtaExpand (Var i es) v a s = do
      fi       <- fromMaybeMP $ findFlexible i (flexVars s)
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        "Found flexible variable " <+> text (show i)
      -- Issue 2888: Do this if there are projections or if it's a singleton
      -- record or if it's unified against a record constructor term. Basically
      -- we need to avoid EtaExpandEquation if EtaExpandVar is possible, or the
      -- forcing translation is unhappy.
      let Dom{unDom = b} = getVarTypeUnraised (varCount s - 1 - i) s
      (d, pars) <- catMaybesMP $ liftTCM $ isEtaRecordType b
      ps        <- fromMaybeMP $ allProjElims es
      sing      <- liftTCM $ (Right True ==) <$> isSingletonRecord d pars
      con       <- liftTCM $ isRecCon v  -- is the other term a record constructor?
      guard $ not (null ps) || sing || con
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        "with projections " <+> prettyTCM (map snd ps)
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        "at record type " <+> prettyTCM d
      return $ EtaExpandVar fi d pars
    shouldEtaExpand _ _ _ _ = mzero

    isRecCon (Con c _ _) = isJust <$> isRecordConstructor (conName c)
    isRecCon _           = return False

etaExpandEquationStrategy :: Int -> UnifyStrategy
etaExpandEquationStrategy k s = do
  let Equal Dom{unDom = a} u v = getEqualityUnraised k s
  (d, pars) <- catMaybesMP $ liftTCM $ addContext tel $ isEtaRecordType a
  sing <- liftTCM $ (Right True ==) <$> isSingletonRecord d pars
  projLeft <- liftTCM $ shouldProject u
  projRight <- liftTCM $ shouldProject v
  guard $ sing || projLeft || projRight
  return $ EtaExpandEquation k d pars
  where
    shouldProject :: Term -> TCM Bool
    shouldProject u = case u of
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
      Dummy s    -> __IMPOSSIBLE_VERBOSE__ s

    tel = varTel s `abstract` telFromList (take k $ telToList $ eqTel s)

simplifySizesStrategy :: Int -> UnifyStrategy
simplifySizesStrategy k s = do
  isSizeName <- liftTCM isSizeNameTest
  let Equal Dom{unDom = a} u v = getEquality k s
  case unEl a of
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
    Equal a u@(Def d es) v@(Def d' es') | d == d' -> do
      -- d must be a data, record or axiom
      def <- liftTCM $ getConstInfo d
      guard $ case theDef def of
                Datatype{} -> True
                Record{}   -> True
                Axiom{}    -> True
                DataOrRecSig{} -> True
                AbstractDefn{} -> False -- True triggers issue #2250
                Function{}   -> False
                Primitive{}  -> False
                GeneralizableVar{} -> __IMPOSSIBLE__
                Constructor{} -> __IMPOSSIBLE__  -- Never a type!
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

injectivePragmaStrategy :: Int -> UnifyStrategy
injectivePragmaStrategy k s = do
  eq <- liftTCM $ eqUnLevel $ getEquality k s
  case eq of
    Equal a u@(Def d es) v@(Def d' es') | d == d' -> do
      -- d must have an injective pragma
      def <- liftTCM $ getConstInfo d
      guard $ defInjective def
      let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
      return $ TypeConInjectivity k d us vs
    _ -> mzero

skipIrrelevantStrategy :: Int -> UnifyStrategy
skipIrrelevantStrategy k s = do
  let Equal a _ _ = getEquality k s
  guard =<< isIrrelevantOrPropM a
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
      dontAssignMetas $ noConstraints $ equalTerm a u v
      return Nothing
      `catchError` \err -> return $ Just err
    withoutK <- liftTCM withoutKOption
    case isReflexive of
      Just err     -> return $ DontKnow []
      _ | withoutK -> return $ DontKnow [UnifyReflexiveEq (varTel s) a u]
      _            -> do
        let (s', sigma) = solveEq k u s
        tellUnifyProof sigma
        Unifies <$> liftTCM (reduceEqTel s')

unifyStep s Solution{ solutionAt   = k
                    , solutionType = dom@Dom{ unDom = a }
                    , solutionVar  = fi@FlexibleVar{ flexVar = i }
                    , solutionTerm = u } = do
  let m = varCount s

  -- Check that the type of the variable is equal to the type of the equation
  -- (not just a subtype), otherwise we cannot instantiate (see Issue 2407).
  let dom'@Dom{ unDom = a' } = getVarType (m-1-i) s
  equalTypes <- liftTCM $ addContext (varTel s) $ do
    reportSDoc "tc.lhs.unify" 45 $ "Equation type: " <+> prettyTCM a
    reportSDoc "tc.lhs.unify" 45 $ "Variable type: " <+> prettyTCM a'
    dontAssignMetas $ noConstraints $ equalType a a'
    return Nothing
    `catchError` \err -> return $ Just err

  -- The conditions on the relevances are as follows (see #2640):
  -- - If the type of the equation is relevant, then the solution must be
  --   usable in a relevant position.
  -- - If the type of the equation is (shape-)irrelevant, then the solution
  --   must be usable in a μ-relevant position where μ is the relevance
  --   of the variable being solved.
  --
  -- Jesper, Andreas, 2018-10-17: the quantity of the equation is morally
  -- always @Quantity0@, since the indices of the data type are runtime erased.
  -- This, we need not change the quantity of the solution.
  let eqrel  = getRelevance dom
      varmod = getModality dom'
      mod    = applyUnless (NonStrict `moreRelevant` eqrel) (setRelevance eqrel)
             $ varmod
  reportSDoc "tc.lhs.unify" 65 $ text $ "Equation modality: " ++ show (getModality dom)
  reportSDoc "tc.lhs.unify" 65 $ text $ "Variable modality: " ++ show varmod
  reportSDoc "tc.lhs.unify" 65 $ text $ "Solution must be usable in a " ++ show mod ++ " position."
  -- Andreas, 2018-10-18
  -- Currently, the modality check that would correspond to the
  -- relevance check has problems with meta-variables created in the type signature,
  -- and thus, in quantity 0, that get into terms using the unifier,
  -- and there are checked to be non-erased, i.e., have quantity ω.
  -- Thus, at the moment wo only check relevances, being aware
  -- that uses of the 0-quantity might create segfaults in the compiled program
  -- situations analogous to #2640 (issue with projecting forced constructor fields).
  --
  -- usable <- liftTCM $ addContext (varTel s) $ usableMod mod u  -- TODO
  usable <- liftTCM $ addContext (varTel s) $ usableRel (getRelevance mod) u
  reportSDoc "tc.lhs.unify" 45 $ "Modality ok: " <+> prettyTCM usable
  unless usable $ reportSLn "tc.lhs.unify" 65 $ "Rejected solution: " ++ show u

  case equalTypes of
    Just err -> return $ DontKnow []
    Nothing | usable -> caseMaybeM (trySolveVar (m-1-i) u s)
      (return $ DontKnow [UnifyRecursiveEq (varTel s) a i u])
      (\(s',sub) -> do
        tellUnifySubst sub
        let (s'', sigma) = solveEq k (applyPatSubst sub u) s'
        tellUnifyProof sigma
        Unifies <$> liftTCM (reduce s''))
    Nothing -> return $ DontKnow []
  where
    trySolveVar i u s = case solveVar i u s of
      Just x  -> return $ Just x
      Nothing -> do
        u <- liftTCM $ normalise u
        s <- liftTCM $ normaliseVarTel s
        return $ solveVar i u s

unifyStep s (Injectivity k a d pars ixs c) = do
  ifM (liftTCM $ consOfHIT $ conName c) (return $ DontKnow []) $ do
  withoutK <- liftTCM withoutKOption
  let n = eqCount s

  -- Get constructor telescope and target indices
  ctype <- (`piApply` pars) . defType <$> liftTCM (getConInfo c)
  addContext (varTel s) $ reportSDoc "tc.lhs.unify" 40 $
    "Constructor type: " <+> prettyTCM ctype
  TelV ctel ctarget <- liftTCM $ telView ctype
  let cixs = case unEl ctarget of
               Def d' es | d == d' ->
                 let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                 in  drop (length pars) args
               _ -> __IMPOSSIBLE__

  -- Get index telescope of the datatype
  dtype    <- (`piApply` pars) . defType <$> liftTCM (getConstInfo d)
  addContext (varTel s) $ reportSDoc "tc.lhs.unify" 40 $
    "Datatype type: " <+> prettyTCM dtype

  -- Split equation telescope into parts before and after current equation
  let (eqListTel1, _ : eqListTel2) = splitAt k $ telToList $ eqTel s
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

    -- Higher-dimensional unification has failed. If not --without-K,
    -- we can simply ignore the higher-dimensional equations and
    -- simplify the equation as in the non-indexed case.
    DontKnow _ | not withoutK -> do
      -- using the same variable names as in the case where hdu succeeds.
      let eqTel1' = eqTel1 `abstract` raise (size eqTel1) ctel
          rho1    = raiseS (size ctel)
          ceq     = ConP c noConPatternInfo $ teleNamedArgs ctel
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


    DontKnow _ -> let n           = eqCount s
                      Equal Dom{unDom = a} u v = getEquality k s
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
  } =
  case u of
    Con h _ _ -> do
      ifM (liftTCM $ consOfHIT $ conName h) (return $ DontKnow []) $ do
        return $ NoUnify $ UnifyConflict (varTel s) u v
    _ -> __IMPOSSIBLE__
unifyStep s Cycle
  { cycleVar        = i
  , cycleOccursIn   = u
  } =
  case u of
    Con h _ _ -> do
      ifM (liftTCM $ consOfHIT $ conName h) (return $ DontKnow []) $ do
        return $ NoUnify $ UnifyCycle (varTel s) i u
    _ -> __IMPOSSIBLE__

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
      RecordFlex ks -> indexWithDefault ImplicitFlex ks j
      ImplicitFlex  -> ImplicitFlex
      DotFlex       -> DotFlex
      OtherFlex     -> OtherFlex

    liftFlexible :: Int -> Int -> Maybe Int
    liftFlexible n j = if j == i then Nothing else Just (if j > i then j + (n-1) else j)

    liftFlexibles :: Int -> FlexibleVars -> FlexibleVars
    liftFlexibles n fs = mapMaybe (traverse $ liftFlexible n) fs

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
      (s', sigma) =  -- newline because of CPP
        solveEq k (DontCare $ unArg $ indexWithDefault __IMPOSSIBLE__ lhs k) s
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
      addContext (varTel s) $
        reportSDoc "tc.lhs.unify" 20 $ "trying unifyStep" <+> prettyTCM step
      x <- unifyStep s step
      case x of
        Unifies s'   -> do
          reportSDoc "tc.lhs.unify" 20 $ "unifyStep successful."
          reportSDoc "tc.lhs.unify" 20 $ "new unifyState:" <+> prettyTCM s'
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
