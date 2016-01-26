{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DoAndIfThenElse            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Agda.TypeChecking.Rules.LHS.Unify
  ( UnificationResult
  , UnificationResult'(..)
  , unifyIndices
  , unifyIndices_ ) where

import Prelude hiding (null)

import Control.Arrow ((***))
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Plus
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.Writer (WriterT(..), MonadWriter(..), Monoid(..))

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.List hiding (null, sort)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)

import Agda.Interaction.Options (optInjectiveTypeConstructors)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.SizedTypes (compareSizes)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Substitute.Pattern
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.MetaVars (assignV, newArgsMetaCtx)
import Agda.TypeChecking.EtaContract
import Agda.Interaction.Options (optInjectiveTypeConstructors, optWithoutK)

import Agda.TypeChecking.Rules.LHS.Problem hiding (Substitution)
-- import Agda.TypeChecking.SyntacticEquality

import Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , MonadError(catchError, throwError)
  )
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
type UnificationResult = UnificationResult' (Telescope, PatternSubstitution)

data UnificationResult' a
  = Unifies  a      -- ^ Unification succeeded.
  | NoUnify  TCErr  -- ^ Terms are not unifiable.
  | DontKnow TCErr  -- ^ Some other error happened, unification got stuck.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

-- | Unify indices.
--
--   In @unifyIndices_ flex a us vs@,
--
--   @a@ is the type eliminated by @us@ and @vs@
--     (usally the type of a constructor),
--     need not be reduced,
--
--   @us@ and @vs@ are the argument lists to unify,
--
--   @flex@ is the set of flexible (instantiable) variabes in @us@ and @vs@.
--
--   The result is the most general unifier of @us@ and @vs@.
unifyIndices_ :: MonadTCM tcm
              => Telescope
              -> FlexibleVars
              -> Type
              -> Args
              -> Args
              -> tcm (Telescope, PatternSubstitution)
unifyIndices_ tel flex a us vs = liftTCM $ do
  r <- unifyIndices tel flex a us vs
  case r of
    Unifies sub   -> return sub
    DontKnow err  -> throwError err
    NoUnify  err  -> throwError err

unifyIndices :: MonadTCM tcm
             => Telescope
             -> FlexibleVars
             -> Type
             -> Args
             -> Args
             -> tcm UnificationResult
unifyIndices tel flex a us vs = liftTCM $ Bench.billTo [Bench.Typing, Bench.CheckLHS, Bench.UnifyIndices] $ do
    reportSDoc "tc.lhs.unify" 10 $
      sep [ text "unifyIndices"
          , nest 2 $ prettyTCM tel
          , nest 2 $ addCtxTel tel $ text (show flex)
          , nest 2 $ addCtxTel tel $ parens (prettyTCM a)
          , nest 2 $ addCtxTel tel $ prettyList $ map prettyTCM us
          , nest 2 $ addCtxTel tel $ prettyList $ map prettyTCM vs
          ]
    initialState    <- initUnifyState tel flex a us vs
    reportSDoc "tc.lhs.unify" 20 $ text "initial unifyState:" <+> prettyTCM initialState
    reportSDoc "tc.lhs.unify" 70 $ text "initial unifyState:" <+> text (show initialState)
    (result,output) <- runUnifyM $ unify initialState rightToLeftStrategy
    return $ fmap (\s -> (varTel s , unifySubst output)) result

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
  , eqLHS    :: [Term]
  , eqRHS    :: [Term]
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
  prettyTCM state = text "UnifyState" <+> nest 2 (vcat $
    [ text "  variable tel:  " <+> prettyTCM gamma
    , text "  flexible vars: " <+> prettyTCM (map flexVar $ flexVars state)
    , text "  equation tel:  " <+> addCtxTel gamma (prettyTCM delta)
    , text "  equations:     " <+> addCtxTel gamma (prettyList_ (zipWith prettyEquality (eqLHS state) (eqRHS state)))
    ])
    where
      gamma = varTel state
      delta = eqTel state
      prettyEquality x y = prettyTCM x <+> text "=?=" <+> prettyTCM y

initUnifyState :: Telescope -> FlexibleVars -> Type -> Args -> Args -> TCM UnifyState
initUnifyState tel flex a us vs = do
  let lhs = map unArg us
      rhs = map unArg vs
      n   = size lhs
  unless (n == size lhs) __IMPOSSIBLE__
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
    Equal (unDom $ (flattenTel eqs) !! k) (lhs !! k) (rhs !! k)

-- | As getEquality, but with the unraised type
getEqualityUnraised :: Int -> UnifyState -> Equality
getEqualityUnraised k UState { eqTel = eqs, eqLHS = lhs, eqRHS = rhs } =
  if k < 0 then __IMPOSSIBLE__ else
    Equal (snd . unDom $ (telToList eqs) !! k) (lhs !! k) (rhs !! k)

getEqInfo :: Int -> UnifyState -> ArgInfo
getEqInfo k UState { eqTel = eqs } =
  if k < 0 then __IMPOSSIBLE__ else domInfo $ telToList eqs !! k

-- | Add a list of equations to the front of the equation telescope
addEqs :: Telescope -> [Term] -> [Term] -> UnifyState -> UnifyState
addEqs tel us vs s =
  s { eqTel = tel `abstract` eqTel s
    , eqLHS = us ++ eqLHS s
    , eqRHS = vs ++ eqRHS s
    }
  where k = size tel

addEq :: Type -> Term -> Term -> UnifyState -> UnifyState
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
      mapMaybe $ \(FlexibleVar h k x) ->
        FlexibleVar h k <$> findIndex (x==) (permPicks perm)

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
solveEq :: Int -> Term -> UnifyState -> UnifyState
solveEq k u s = s
    { eqTel    = applyUnder k (eqTel s) (raise k u)
    , eqLHS    = dropAt k $ eqLHS s
    , eqRHS    = dropAt k $ eqRHS s
    }
  where


-- | Simplify the k'th equation with the given value (which can depend on other
--   equation variables). Returns Nothing if there is a cycle.
simplifyEq :: Int -> Term -> UnifyState -> Maybe UnifyState
simplifyEq k u s = case instantiateTelescope (eqTel s) k u of
  Nothing -> Nothing
  Just (tel' , sigma , rho) -> Just $ UState
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
    , injectArgsLeft     :: Args
    , injectArgsRight    :: Args
    }
  | Conflict
    { conflictAt         :: Int
    , conflictDatatype   :: QName
    , conflictParameters :: Args
    , conflictConLeft    :: ConHead
    , conflictConRight   :: ConHead
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
    , dataStrategy
    , literalStrategy
    , etaExpandVarStrategy
    , etaExpandEquationStrategy
    , injectiveTypeConStrategy
    , simplifySizesStrategy
    , checkEqualityStrategy
    ]

-- | Returns true if the variables 0..k-1 don't occur in x
isHom :: (Free' a All, Subst Term a) => Int -> a -> Maybe a
isHom n x = do
  guard $ getAll $ runFree (\ (i,_) -> All (i >= n)) IgnoreNot x
  --guard $ null $ allFreeVars x `IntSet.intersection` IntSet.fromAscList [0..k-1]
  return $ raise (-n) x

isEtaVar :: Term -> Type -> TCM (Maybe Int)
isEtaVar u a = runMaybeT $ isEtaVarG u a Nothing []
  where
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
            (_, fa) <- MaybeT $ projectTyped u a f
            isEtaVarG (u `applyE` [Proj f]) fa mi (es++[Proj f])
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

    areEtaVarElims :: Term -> Type -> Elims -> [Elim' Int] -> MaybeT TCM ()
    areEtaVarElims u a []    []    = return ()
    areEtaVarElims u a []    (_:_) = mzero
    areEtaVarElims u a (_:_) []    = mzero
    areEtaVarElims u a (Proj f : es) (Proj f' : es') = do
      guard $ f == f'
      a       <- liftTCM $ reduce a
      (_, fa) <- MaybeT $ projectTyped u a f
      areEtaVarElims (u `applyE` [Proj f]) fa es es'
    areEtaVarElims u a (Proj  _ : _ ) (Apply _ : _  ) = __IMPOSSIBLE__
    areEtaVarElims u a (Apply _ : _ ) (Proj  _ : _  ) = __IMPOSSIBLE__
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
  (mi, mj) <- liftTCM $ addCtxTel (varTel s) $ (,) <$> isEtaVar u ha <*> isEtaVar v ha
  liftTCM $ reportSDoc "tc.lhs.unify" 30 $ text "isEtaVar results: " <+> text (show [mi,mj])
  case (mi, mj) of
    (Just i, Just j)
     | i == j -> return $ Deletion k ha (var i) (var i)
    (Just i, Just j)
     | Just fi <- findFlexible i flex
     , Just fj <- findFlexible j flex -> do
       let choice = chooseFlex fi fj
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "fi = " <+> text (show fi)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "fj = " <+> text (show fj)
       liftTCM $ reportSDoc "tc.lhs.unify" 40 $ text "chooseFlex: " <+> text (show choice)
       case choice of
         ChooseLeft   -> return $ Solution k ha i v
         ChooseRight  -> return $ Solution k ha j u
         ExpandBoth   -> mzero -- This should be taken care of by etaExpandEquationStrategy
         ChooseEither -> return $ Solution k ha j u
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
  Equal a u v <- liftTCM $ eqConstructorForm =<< eqUnLevel (getEquality k s)
  case a of
    El _ (Def d es) -> do
      npars <- mcatMaybes $ liftTCM $ getNumberOfParameters d
      let (pars,ixs) = splitAt npars $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      hpars <- mfromMaybe $ isHom (eqCount s) pars
      liftTCM $ reportSDoc "tc.lhs.unify" 40 $ addContext (varTel s `abstract` eqTel s) $
        text "Found equation at datatype " <+> prettyTCM d
         <+> text " with (homogeneous) parameters " <+> prettyTCM hpars
      case (u, v) of
        (MetaV m es, Con c vs  ) -> do
          us <- mcatMaybes $ liftTCM $ instMetaCon m es d hpars c
          return $ Injectivity k a d hpars ixs c us vs
        (Con c us  , MetaV m es) -> do
          vs <- mcatMaybes $ liftTCM $ instMetaCon m es d hpars c
          return $ Injectivity k a d hpars ixs c us vs
        (Con c us  , Con c' vs ) | c == c' -> return $ Injectivity k a d hpars ixs c us vs
        (Con c _   , Con c' _  ) -> return $ Conflict k d hpars c c'
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
    instMetaCon :: MetaId -> Elims -> QName -> Args -> ConHead -> TCM (Maybe Args)
    instMetaCon m es d pars c = case allApplyElims es of
      Just us -> do
          margs <- do
            -- The new metas should have the same dependencies as the original meta
            mv <- lookupMeta m

            ctype <- (`piApply` pars) . defType <$> liftTCM (getConstInfo $ conName c)
            TelV tel _ <- telView ctype
            let b'  = telePi tel (sort Prop)

            withMetaInfo' mv $ do
              tel <- getContextTelescope
              -- important: create the meta in the same environment as the original meta
              newArgsMetaCtx b' tel us
          noConstraints $ assignV DirEq m us (Con c margs)
          return $ Just margs
        `catchError` \_ -> return Nothing
      Nothing -> return Nothing

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
        text "with projections " <+> prettyTCM ps
      let b = getVarTypeUnraised (varCount s - 1 - i) s
      (d, pars) <- mcatMaybes $ liftTCM $ isEtaRecordType b
      liftTCM $ reportSDoc "tc.lhs.unify" 50 $
        text "at record type " <+> prettyTCM d
      return $ EtaExpandVar fi d pars
    shouldEtaExpand _ _ _ = mzero

etaExpandEquationStrategy :: Int -> UnifyStrategy
etaExpandEquationStrategy k s = do
  let Equal a u v = getEqualityUnraised k s
  (d, pars) <- mcatMaybes $ liftTCM $ addCtxTel tel $ isEtaRecordType a
  sing <- liftTCM $ (Right True ==) <$> isSingletonRecord d pars
  projLeft <- liftTCM $ shouldProject u
  projRight <- liftTCM $ shouldProject v
  guard $ sing || projLeft || projRight
  return $ EtaExpandEquation k d pars
  where
    shouldProject :: Term -> TCM Bool
    shouldProject u = case ignoreSharing u of
      Def f es   -> usesCopatterns f
      Con c us   -> isJust <$> isRecordConstructor (conName c)

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
                _          -> False
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
  , unifyLog   :: UnifyLog
  }

instance Monoid UnifyOutput where
  mempty        = UnifyOutput IdS []
  x `mappend` y = UnifyOutput
    { unifySubst = unifySubst y `composeS` unifySubst x
    , unifyLog   = unifyLog x ++ unifyLog y
    }

type UnifyM a = WriterT UnifyOutput TCM a

tellUnifySubst :: PatternSubstitution -> UnifyM ()
tellUnifySubst sub = do
  tell $ UnifyOutput sub []

writeUnifyLog :: UnifyLogEntry -> UnifyM ()
writeUnifyLog x = tell $ UnifyOutput IdS [x]

runUnifyM :: UnifyM a -> TCM (a,UnifyOutput)
runUnifyM = runWriterT

unifyStep :: UnifyState -> UnifyStep -> UnifyM (UnificationResult' UnifyState)

unifyStep s Deletion{ deleteAt = k , deleteType = a , deleteLeft = u , deleteRight = v } =
  liftTCM $ do
    addCtxTel (varTel s) $ noConstraints $ equalTerm a u v
    ifM ((optWithoutK <$> pragmaOptions) `and2M` (not <$> isSet (unEl a)))
    {-then-} (DontKnow <$> withoutKErr)
    {-else-} (Unifies  <$> reduceEqTel (solveEq k u s))
  `catchError` \err -> return $ DontKnow err
  where
    withoutKErr = addContext (varTel s) $ typeError_ $ WithoutKError a u u

unifyStep s Solution{ solutionAt = k , solutionType = a , solutionVar = i , solutionTerm = u } = do
  let m = varCount s
  caseMaybeM (trySolveVar (m-1-i) u s) (DontKnow <$> err) $ \(s',sub) -> do
    tellUnifySubst sub
    Unifies <$> liftTCM (reduce $ solveEq k (applyPatSubst sub u) s')
  where
    trySolveVar i u s = case solveVar i u s of
      Just x  -> return $ Just x
      Nothing -> do
        u <- liftTCM $ normalise u
        s <- liftTCM $ normaliseVarTel s
        return $ solveVar i u s
    err = addContext (varTel s) $ typeError_ $ UnificationRecursiveEq a i u

unifyStep s (Injectivity k a d pars ixs c lhs rhs) = do
  withoutK <- liftTCM $ optWithoutK <$> pragmaOptions
  ctype    <- (`piApply` pars) . defType <$> liftTCM (getConstInfo $ conName c)
  reportSDoc "tc.lhs.unify" 40 $ text "Constructor type: " <+> prettyTCM ctype
  TelV ctel ctarget <- liftTCM $ telView ctype
  (lhs, rhs) <- liftTCM $ reduce (lhs,rhs)
  case ignoreSharing  $ unEl ctarget of
    Def d' es | d == d' -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          cixs = map unArg $ drop (length pars) args
          ceq  = Con c $ teleArgs ctel
      let mis  = mfilter fastDistinct $ forM ixs $ \ix ->
                   case ignoreSharing $ unArg ix of
                     Var i [] | i < eqCount s -> Just i
                     _        -> Nothing
      case mis of
        Nothing | withoutK -> DontKnow <$> err
        Nothing -> do
          return $ Unifies $
            addEqs ctel (map unArg lhs) (map unArg rhs) $
              solveEq k ceq s
        Just is -> do
          let n  = eqCount s
              js = is ++ [n-1-k]
          caseMaybeM (trySplitTelescopeExact js (eqTel s)) (DontKnow <$> err) $
            \(SplitTel tel1 tel2 perm) -> do
            reportSDoc "tc.lhs.unify" 40 $ addCtxTel (varTel s) $ sep $
              [ text "split telescope" <+> prettyTCM (eqTel s) <+> text ("at " ++ show js)
              , text "  into" <+> prettyTCM tel1
              , text "  and " <+> addCtxTel tel1 (prettyTCM tel2)
              , text "  perm =" <+> text (show perm)
              ]
            let n1   = size tel1
                n2   = size tel2
                sub1 = renaming perm :: Substitution -- or renamingR?
                sub2 = (ceq : reverse cixs) ++# raiseS (size ctel)
            Unifies <$> liftTCM (reduceEqTel $ s
              { eqTel    = ctel `abstract` (applySubst sub2 tel2)
              , eqLHS    = map unArg lhs ++ drop n1 (permute perm $ eqLHS s)
              , eqRHS    = map unArg rhs ++ drop n1 (permute perm $ eqRHS s)
              })
    _ -> __IMPOSSIBLE__
  where
    n = eqCount s

    err = addContext (varTel s `abstract` eqTel s) $ typeError_
        (UnifyIndicesNotVars
          a
          (Con c $ raise n lhs)
          (Con c $ raise n rhs)
          ixs)

    trySplitTelescopeExact js tel = case splitTelescopeExact js tel of
      Just x  -> return $ Just x
      Nothing -> do
        tel <- liftTCM $ normalise tel
        return $ splitTelescopeExact js tel

unifyStep s Conflict
  { conflictConLeft    = c
  , conflictConRight   = c'
  } = NoUnify <$> addContext (varTel s)
        (typeError_ $ UnifyConflict c c')

unifyStep s Cycle
  { cycleVar        = i
  , cycleOccursIn   = u
  } = NoUnify <$> addContext (varTel s)
        (typeError_ $ UnifyCycle i u)

unifyStep s EtaExpandVar{ expandVar = fi, expandVarRecordType = d , expandVarParameters = pars } = do
  delta   <- liftTCM $ (`apply` pars) <$> getRecordFieldTypes d
  c       <- liftTCM $ getRecordConstructor d
  let nfields         = size delta
      (varTel', rho)  = expandTelescopeVar (varTel s) (m-1-i) delta c
      projectFlexible = [ FlexibleVar (flexHiding fi) (projFlexKind j) (i+j) | j <- [0..nfields-1] ]
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
  Unifies <$> liftTCM (reduceEqTel $ s
    { eqTel    = fst $ expandTelescopeVar (eqTel s) k delta c
    , eqLHS    = lhs
    , eqRHS    = rhs
    })
  where
    expandKth us = do
      let (us1,v:us2) = fromMaybe __IMPOSSIBLE__ $ splitExactlyAt k us
      vs <- liftTCM $ map unArg . snd <$> etaExpandRecord d pars v
      vs <- liftTCM $ reduce vs
      return $ us1 ++ vs ++ us2

unifyStep s LitConflict
  { litType          = a
  , litConflictLeft  = l
  , litConflictRight = l'
  } = NoUnify <$> addContext (varTel s)
        (typeError_ $ UnequalTerms CmpEq (Lit l) (Lit l') a)

unifyStep s (StripSizeSuc k u v) = do
  sz <- liftTCM sizeType
  return $ Unifies $ s
    { eqTel = unflattenTel (teleNames $ eqTel s) $
        updateAt k (fmap $ const sz) $ flattenTel $ eqTel s --TODO: is this necessary?
    , eqLHS = updateAt k (const u) $ eqLHS s
    , eqRHS = updateAt k (const v) $ eqRHS s
    }

unifyStep s (SkipIrrelevantEquation k) = do
  let lhs = eqLHS s
  return $ Unifies $ solveEq k (DontCare (lhs !! k)) s

unifyStep s (TypeConInjectivity k d us vs) = do
  dtype <- defType <$> liftTCM (getConstInfo d)
  TelV dtel _ <- liftTCM $ telView dtype
  let n = eqCount s
      m   = size dtel
      deq = Def d $ map Apply $ teleArgs dtel
  Unifies <$> liftTCM (reduceEqTel $ s
    { eqTel = dtel `abstract` applyUnder k (eqTel s) (raise k deq)
    , eqLHS = map unArg us ++ dropAt k (eqLHS s)
    , eqRHS = map unArg vs ++ dropAt k (eqRHS s)
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
      reportSDoc "tc.lhs.unify" 20 $ text "trying unifyStep" <+> text (show step)
      x <- unifyStep s step
      case x of
        Unifies s'   -> do
          reportSDoc "tc.lhs.unify" 20 $ text "unifyStep successful."
          reportSDoc "tc.lhs.unify" 20 $ text "new unifyState:" <+> prettyTCM s'
          writeUnifyLog $ UnificationStep s step
          return x
        NoUnify{}    -> return x
        DontKnow err -> do
          y <- fallback
          case y of
            DontKnow{} -> return x
            _          -> return y

    failure :: UnifyM (UnificationResult' a)
    failure = do
      err <- addContext (varTel s) $ typeError_ $
               UnificationStuck (eqTel s) (eqLHS s) (eqRHS s)
      return $ DontKnow err

isSet :: Term -> TCM Bool
isSet a = do
  a <- reduce a
  case ignoreSharing a of
    Def d es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      Defn{ defType = dtype, theDef = def } <- getConstInfo d
      reportSDoc "tc.lhs.unify.isset" 50 $ text "Checking whether " <+> prettyTCM a <+> text " is a set..."
      case def of
        Datatype{ dataPars = npars, dataCons = cs, dataMutual = [], dataAbstr = ConcreteDef } -> do
           let pars       = take npars args
               TelV tel _ = telView' $ dtype `piApply` pars
               ixtypes    = map (unEl . unDom) $ flattenTel tel
           ifNotM (allM ixtypes isSet) (return False) $ allM cs $ \c -> do
             ctype <- defType <$> getConstInfo c
             checkConstructorType d $ ctype `piApply` pars
        Record{ recConType = ctype } -> checkConstructorType d $ ctype `piApply` args
        _ -> return False
    _ -> return False
  where
    checkConstructorType :: QName -> Type -> TCM Bool
    checkConstructorType d a = do
      let TelV tel _ = telView' a
      allM (map (unEl . unDom) $ flattenTel tel) $ \b -> case ignoreSharing b of
        Def d' _ | d == d' -> return True
        _ -> isSet b
