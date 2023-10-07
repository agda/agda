{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.LHS.Unify.Types where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Writer (WriterT(..), MonadWriter(..))

import Data.Foldable (toList)
import Data.DList (DList)
import qualified Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.LHS.Problem

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible

----------------------------------------------------
-- Equalities
----------------------------------------------------

data Equality = Equal
  { _eqType  :: Dom Type
  , _eqLeft  :: Term
  , _eqRight :: Term
  }

-- Jesper, 2020-01-19: The type type lives in the context of the
-- variables+equations, while the lhs/rhs only depend on the
-- variables, so there is no way to give a correct Reduce instance.
-- WRONG:
-- instance Reduce Equality where
--   reduce' (Equal a u v) = Equal <$> reduce' a <*> reduce' u <*> reduce' v

eqConstructorForm :: HasBuiltins m => Equality -> m Equality
eqConstructorForm (Equal a u v) = Equal a <$> constructorForm u <*> constructorForm v

eqUnLevel :: (HasBuiltins m, HasOptions m) => Equality -> m Equality
eqUnLevel (Equal a u v) = Equal a <$> unLevel u <*> unLevel v
  where
    unLevel (Level l) = reallyUnLevelView l
    unLevel u         = return u

----------------------------------------------------
-- Unify state
----------------------------------------------------

data UnifyState = UState
  { varTel   :: Telescope     -- ^ Don't reduce!
  , flexVars :: FlexibleVars
  , eqTel    :: Telescope     -- ^ Can be reduced eagerly.
  , eqLHS    :: [Arg Term]    -- ^ Ends up in dot patterns (should not be reduced eagerly).
  , eqRHS    :: [Arg Term]    -- ^ Ends up in dot patterns (should not be reduced eagerly).
  } deriving (Show)
-- Issues #3578 and #4125: avoid unnecessary reduction in unifier.

lensVarTel   :: Lens' UnifyState Telescope
lensVarTel   f s = f (varTel s) <&> \ tel -> s { varTel = tel }
{-# INLINE lensVarTel #-}
--UNUSED Liang-Ting Chen 2019-07-16
--lensFlexVars :: Lens' UnifyState FlexibleVars
--lensFlexVars f s = f (flexVars s) <&> \ flex -> s { flexVars = flex }

lensEqTel    :: Lens' UnifyState Telescope
lensEqTel    f s = f (eqTel s) <&> \ x -> s { eqTel = x }
{-# INLINE lensEqTel #-}

--UNUSED Liang-Ting Chen 2019-07-16
--lensEqLHS    :: Lens' UnifyState Args
--lensEqLHS    f s = f (eqLHS s) <&> \ x -> s { eqLHS = x }

--UNUSED Liang-Ting Chen 2019-07-16
--lensEqRHS    :: Lens' UnifyState Args
--lensEqRHS    f s = f (eqRHS s) <&> \ x -> s { eqRHS = x }

-- UNUSED Andreas, 2019-10-14
-- instance Reduce UnifyState where
--   reduce' (UState var flex eq lhs rhs) =
--     UState <$> reduce' var
--            <*> pure flex
--            <*> reduce' eq
--            <*> reduce' lhs
--            <*> reduce' rhs

-- Andreas, 2019-10-14, issues #3578 and #4125:
-- | Don't ever reduce the whole 'varTel', as it will destroy
-- readability of the context in interactive editing!
-- To make sure this insight is not lost, the following
-- dummy instance should prevent a proper 'Reduce' instance for 'UnifyState'.
instance Reduce UnifyState where
  reduce' = __IMPOSSIBLE__

--UNUSED Liang-Ting Chen 2019-07-16
--reduceEqTel :: UnifyState -> TCM UnifyState
--reduceEqTel = lensEqTel reduce

-- UNUSED Andreas, 2019-10-14
-- instance Normalise UnifyState where
--   normalise' (UState var flex eq lhs rhs) =
--     UState <$> normalise' var
--            <*> pure flex
--            <*> normalise' eq
--            <*> normalise' lhs
--            <*> normalise' rhs

instance PrettyTCM UnifyState where
  prettyTCM state = "UnifyState" $$ nest 2 (vcat $
    [ "variable tel:  " <+> prettyTCM gamma
    , "flexible vars: " <+> pshow (map flexVarF $ flexVars state)
    , "equation tel:  " <+> addContext gamma (prettyTCM delta)
    , "equations:     " <+> addContext gamma (prettyList_ (zipWith prettyEquality (eqLHS state) (eqRHS state)))
    ])
    where
      flexVarF fi = (flexVar fi, flexForced fi)
      gamma = varTel state
      delta = eqTel state
      prettyEquality x y = prettyTCM x <+> "=?=" <+> prettyTCM y

initUnifyState
  :: PureTCM m
  => Telescope -> FlexibleVars -> Type -> Args -> Args -> m UnifyState
initUnifyState tel flex a lhs rhs = do
  (tel, a, lhs, rhs) <- instantiateFull (tel, a, lhs, rhs)
  let n = size lhs
  unless (n == size rhs) __IMPOSSIBLE__
  TelV eqTel _ <- telView a
  unless (n == size eqTel) __IMPOSSIBLE__
  return $ UState tel flex eqTel lhs rhs
  -- Andreas, 2019-02-23, issue #3578: do not eagerly reduce
  -- reduce $ UState tel flex eqTel lhs rhs

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

getReducedEquality
  :: (MonadReduce m, MonadAddContext m)
  => Int -> UnifyState -> m Equality
getReducedEquality k s = do
  let Equal a u v = getEquality k s
  addContext (varTel s) $ Equal
    <$> addContext (eqTel s) (reduce a)
    <*> reduce u
    <*> reduce v

-- | As getEquality, but with the unraised type
getEqualityUnraised :: Int -> UnifyState -> Equality
getEqualityUnraised k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
    Equal (snd <$> indexWithDefault __IMPOSSIBLE__ (telToList eqs) k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ lhs k)
          (unArg $ indexWithDefault __IMPOSSIBLE__ rhs k)

getReducedEqualityUnraised
  :: (MonadReduce m, MonadAddContext m)
  => Int -> UnifyState -> m Equality
getReducedEqualityUnraised k s = do
  let Equal a u v = getEqualityUnraised k s
  addContext (varTel s) $ Equal
    <$> addContext (telFromList $ take k $ telToList $ eqTel s) (reduce a)
    <*> reduce u
    <*> reduce v

--UNUSED Liang-Ting Chen 2019-07-16
--getEqInfo :: Int -> UnifyState -> ArgInfo
--getEqInfo k UState { eqTel = eqs } =
--  domInfo $ indexWithDefault __IMPOSSIBLE__ (telToList eqs) k
--
---- | Add a list of equations to the front of the equation telescope
--addEqs :: Telescope -> [Arg Term] -> [Arg Term] -> UnifyState -> UnifyState
--addEqs tel us vs s =
--  s { eqTel = tel `abstract` eqTel s
--    , eqLHS = us ++ eqLHS s
--    , eqRHS = vs ++ eqRHS s
--    }
--  where k = size tel
--
--addEq :: Type -> Arg Term -> Arg Term -> UnifyState -> UnifyState
--addEq a u v = addEqs (ExtendTel (defaultDom a) (Abs underscore EmptyTel)) [u] [v]



-- | Instantiate the k'th variable with the given value.
--   Returns Nothing if there is a cycle.
solveVar :: Int             -- ^ Index @k@
         -> DeBruijnPattern -- ^ Solution @u@
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
      mapMaybe $ \(FlexibleVar ai fc k p x) ->
        FlexibleVar ai fc k p <$> List.elemIndex x (permPicks perm)

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

--UNUSED Liang-Ting Chen 2019-07-16
---- | Simplify the k'th equation with the given value (which can depend on other
----   equation variables). Returns Nothing if there is a cycle.
--simplifyEq :: Int -> Term -> UnifyState -> Maybe (UnifyState, PatternSubstitution)
--simplifyEq k u s = case instantiateTelescope (eqTel s) k u of
--  Nothing -> Nothing
--  Just (tel' , sigma , rho) -> Just $ (,sigma) $ UState
--    { varTel   = varTel s
--    , flexVars = flexVars s
--    , eqTel    = tel'
--    , eqLHS    = permute rho $ eqLHS s
--    , eqRHS    = permute rho $ eqRHS s
--    }
--
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
    , solutionSide       :: Either () ()
      -- ^ side of the equation where the variable is.
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
    Solution k a i u s -> "Solution" $$ nest 2 (vcat $
      [ "position:   " <+> text (show k)
      , "type:       " <+> prettyTCM a
      , "variable:   " <+> text (show (flexVar i, flexPos i, flexForced i, flexKind i))
      , "term:       " <+> prettyTCM u
      , "side:       " <+> text (show s)
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


----------------------------------------------------
-- Unify Log and monad
----------------------------------------------------

data UnifyLogEntry
 -- = UnificationDone  UnifyState
  = UnificationStep UnifyState UnifyStep UnifyOutput

type UnifyLog = [(UnifyLogEntry,UnifyState)]

-- | This variant of 'UnifyLog' is used to ensure that 'tell' is not
-- expensive.
type UnifyLog' = DList (UnifyLogEntry, UnifyState)

-- Given varΓ ⊢ eqΓ, varΓ ⊢ us, vs : eqΓ
data UnifyOutput = UnifyOutput
  { unifySubst :: PatternSubstitution -- varΓ' ⊢ σ : varΓ
  , unifyProof :: PatternSubstitution -- varΓ',eqΓ' ⊢ ps : eqΓ[σ]
                                      -- varΓ', us' =_eqΓ' vs' ⊢ ap(ps) : us[σ] =_{eqΓ[σ]} vs[σ]
--  , unifyLog   :: UnifyLog
  }

instance Semigroup UnifyOutput where
  x <> y = UnifyOutput
    { unifySubst = unifySubst y `composeS` unifySubst x
    , unifyProof = unifyProof y `composeS` unifyProof x
--    , unifyLog   = unifyLog x ++ unifyLog y
    }

instance Monoid UnifyOutput where
  mempty  = UnifyOutput IdS IdS -- []
  mappend = (<>)

type UnifyLogT m a = WriterT UnifyLog' m a

type UnifyStepT m a = WriterT UnifyOutput m a

tellUnifySubst :: MonadWriter UnifyOutput m => PatternSubstitution -> m ()
tellUnifySubst sub = tell $ UnifyOutput sub IdS

tellUnifyProof :: MonadWriter UnifyOutput m => PatternSubstitution -> m ()
tellUnifyProof sub = tell $ UnifyOutput IdS sub

writeUnifyLog ::
  MonadWriter UnifyLog' m => (UnifyLogEntry, UnifyState) -> m ()
writeUnifyLog x = tell (singleton x) -- UnifyOutput IdS IdS [x]

runUnifyLogT :: Functor m => UnifyLogT m a -> m (a, UnifyLog)
runUnifyLogT m = mapSnd toList <$> runWriterT m
