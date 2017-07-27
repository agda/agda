{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances     #-}

{- |  Non-linear matching of the lhs of a rewrite rule against a
      neutral term.

Given a lhs

  Δ ⊢ lhs : B

and a candidate term

  Γ ⊢ t : A

we seek a substitution Γ ⊢ σ : Δ such that

  Γ ⊢ B[σ] = A   and
  Γ ⊢ lhs[σ] = t : A

-}

module Agda.TypeChecking.Rewriting.NonLinMatch where

import Prelude hiding (null, sequence)

import Control.Arrow (first, second)
import Control.Monad.State

import Debug.Trace
import System.IO.Unsafe

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable ( foldMap )
#endif

import Data.Maybe
import Data.Traversable (Traversable,traverse)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (elemIndex)
import Data.Monoid

import Agda.Syntax.Common
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Internal

import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level (levelView', unLevel, reallyUnLevelView, subLevel)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primLevelSuc, primLevelMax)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records (isRecordConstructor)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (permuteTel)

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first argument indicates the relevance we are working under: if this
--   is Irrelevant, then we construct a pattern that never fails to match.
--   The second argument is the number of bound variables (from pattern lambdas).

class PatternFrom a b where
  patternFrom :: Relevance -> Int -> a -> TCM b

instance (PatternFrom a b) => PatternFrom [a] [b] where
  patternFrom r k = traverse $ patternFrom r k

instance (PatternFrom a b) => PatternFrom (Arg a) (Arg b) where
  patternFrom r k u = let r' = r `composeRelevance` getRelevance u
                      in  traverse (patternFrom r' k) u

instance (PatternFrom a NLPat) => PatternFrom (Elim' a) (Elim' NLPat) where
  patternFrom r k (Apply u) = let r' = r `composeRelevance` getRelevance u
                              in  Apply <$> traverse (patternFrom r' k) u
  patternFrom r k (IApply x y u) = let r' = r `composeRelevance` Relevant
                                   in  IApply <$> patternFrom r' k x
                                              <*> patternFrom r' k y
                                              <*> patternFrom r' k u
  patternFrom r k (Proj o f) = return $ Proj o f

instance (PatternFrom a b) => PatternFrom (Dom a) (Dom b) where
  patternFrom r k = traverse $ patternFrom r k

instance PatternFrom Type NLPType where
  patternFrom r k a = NLPType <$> patternFrom r k (getSort a)
                              <*> patternFrom r k (unEl a)

instance PatternFrom Sort NLPat where
  patternFrom r k s = do
    s <- reduce s
    let done = return PWild
    case s of
      Type l   -> patternFrom Irrelevant k (Level l)
      Prop     -> done
      Inf      -> done
      SizeUniv -> done
      DLub _ _ -> done

instance PatternFrom Term NLPat where
  patternFrom r k v = do
    v <- unLevel =<< reduce v
    let done = if isIrrelevant r then
                 return PWild
               else
                 return $ PTerm v
    case ignoreSharing v of
      Var i es
       | i < k     -> PBoundVar i <$> patternFrom r k es
       | otherwise -> do
         -- The arguments of `var i` should be distinct bound variables
         -- in order to build a Miller pattern
         let mbvs = mfilter fastDistinct $ forM es $ \e -> do
                      e <- isApplyElim e
                      case ignoreSharing $ unArg e of
                        Var j [] | j < k -> Just $ e $> j
                        _                -> Nothing
         case mbvs of
           Just bvs -> do
             let i' = i-k
                 allBoundVars = IntSet.fromList (downFrom k)
                 ok = not (isIrrelevant r) ||
                      IntSet.fromList (map unArg bvs) == allBoundVars
             if ok then return (PVar i bvs) else done
           Nothing -> done
      Lam i t  -> PLam i <$> patternFrom r k t
      Lit{}    -> done
      Def f es | isIrrelevant r -> done
      Def f es -> do
        Def lsuc [] <- ignoreSharing <$> primLevelSuc
        Def lmax [] <- ignoreSharing <$> primLevelMax
        case es of
          [x]     | f == lsuc -> done
          [x , y] | f == lmax -> done
          _                   -> PDef f <$> patternFrom r k es
      Con c ci vs | isIrrelevant r -> do
        mr <- isRecordConstructor (conName c)
        case mr of
          Just (_, def) | recEtaEquality def ->
            PDef (conName c) <$> patternFrom r k (Apply <$> vs)
          _ -> done
      Con c ci vs -> PDef (conName c) <$> patternFrom r k (Apply <$> vs)
      Pi a b | isIrrelevant r -> done
      Pi a b   -> PPi <$> patternFrom r k a <*> patternFrom r k b
      Sort s   -> done
      Level l  -> __IMPOSSIBLE__
      DontCare{} -> return PWild
      MetaV{}    -> __IMPOSSIBLE__
      Shared{}   -> __IMPOSSIBLE__

instance (PatternFrom a b) => PatternFrom (Abs a) (Abs b) where
  patternFrom r k (Abs name x)   = Abs name   <$> patternFrom r (k+1) x
  patternFrom r k (NoAbs name x) = NoAbs name <$> patternFrom r k x

-- | Monad for non-linear matching.
type NLM = ExceptT Blocked_ (StateT NLMState ReduceM)

data NLMState = NLMState
  { _nlmSub   :: Sub
  , _nlmEqs   :: PostponedEquations
  }

instance Null NLMState where
  empty  = NLMState { _nlmSub = empty , _nlmEqs = empty }
  null s = null (s^.nlmSub) && null (s^.nlmEqs)

nlmSub :: Lens' Sub NLMState
nlmSub f s = f (_nlmSub s) <&> \x -> s {_nlmSub = x}

nlmEqs :: Lens' PostponedEquations NLMState
nlmEqs f s = f (_nlmEqs s) <&> \x -> s {_nlmEqs = x}

liftRed :: ReduceM a -> NLM a
liftRed = lift . lift

runNLM :: NLM () -> ReduceM (Either Blocked_ NLMState)
runNLM nlm = do
  (ok,out) <- runStateT (runExceptT nlm) empty
  case ok of
    Left block -> return $ Left block
    Right _    -> return $ Right out

matchingBlocked :: Blocked_ -> NLM ()
matchingBlocked = throwError

-- | Add substitution @i |-> v@ to result of matching.
tellSub :: Relevance -> Int -> Term -> NLM ()
tellSub r i v = do
  old <- IntMap.lookup i <$> use nlmSub
  case old of
    Nothing -> nlmSub %= IntMap.insert i (r,v)
    Just (r',v')
      | isIrrelevant r  -> return ()
      | isIrrelevant r' -> nlmSub %= IntMap.insert i (r,v)
      | otherwise       -> whenJustM (liftRed $ equal v v') matchingBlocked

tellEq :: Telescope -> Telescope -> Term -> Term -> NLM ()
tellEq gamma k u v = do
  traceSDoc "rewriting" 60 (sep
               [ text "adding equality between" <+> addContext (gamma `abstract` k) (prettyTCM u)
               , text " and " <+> addContext k (prettyTCM v) ]) $ do
  nlmEqs %= (PostponedEquation k u v:)

type Sub = IntMap (Relevance, Term)

-- | Matching against a term produces a constraint
--   which we have to verify after applying
--   the substitution computed by matching.
data PostponedEquation = PostponedEquation
  { eqFreeVars :: Telescope -- ^ Telescope of free variables in the equation
  , eqLhs :: Term     -- ^ Term from pattern, living in pattern context.
  , eqRhs :: Term     -- ^ Term from scrutinee, living in context where matching was invoked.
  }
type PostponedEquations = [PostponedEquation]

-- | Match a non-linear pattern against a neutral term,
--   returning a substitution.

class Match a b where
  match :: Relevance  -- ^ Are we currently matching in an irrelevant context?
        -> Telescope  -- ^ The telescope of pattern variables
        -> Telescope  -- ^ The telescope of lambda-bound variables
        -> a          -- ^ The pattern to match
        -> b          -- ^ The term to be matched against the pattern
        -> NLM ()

instance Match a b => Match [a] [b] where
  match r gamma k ps vs
    | length ps == length vs = zipWithM_ (match r gamma k) ps vs
    | otherwise              = matchingBlocked $ NotBlocked ReallyNotBlocked ()

instance Match a b => Match (Arg a) (Arg b) where
  match r gamma k p v = let r' = r `composeRelevance` getRelevance p
                        in  match r' gamma k (unArg p) (unArg v)

instance Match a b => Match (Elim' a) (Elim' b) where
  match r gamma k p v =
   case (p, v) of
     -- The types should ensure that the endpoints are the same.
     (IApply _ _ p,IApply _ _ v) ->
                           let r' = r `composeRelevance` Relevant
                           in  match r' gamma k p v
     (Apply p, Apply v) -> let r' = r `composeRelevance` getRelevance p
                           in  match r' gamma k p v
     (Proj _ x, Proj _ y) -> if x == y then return () else
                             traceSDoc "rewriting" 80 (sep
                               [ text "mismatch between projections " <+> prettyTCM x
                               , text " and " <+> prettyTCM y ]) mzero
     (Apply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , Apply{}) -> __IMPOSSIBLE__
     (IApply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , IApply{}) -> __IMPOSSIBLE__
     (IApply{}, Apply{} ) -> __IMPOSSIBLE__
     (Apply{} , IApply{}) -> __IMPOSSIBLE__

instance Match a b => Match (Dom a) (Dom b) where
  match r gamma k p v = match r gamma k (C.unDom p) (C.unDom v)

instance Match NLPType Type where
  match r gamma k (NLPType lp p) (El s a) = match r gamma k lp s >> match r gamma k p a

instance Match NLPat Sort where
  match r gamma k p s = case (p , s) of
    (PWild , _     ) -> return ()
    (p     , Type l) -> match Irrelevant gamma k p l
    _                -> matchingBlocked $ NotBlocked ReallyNotBlocked ()

instance (Match a b, Subst t1 a, Subst t2 b) => Match (Abs a) (Abs b) where
  match r gamma k (Abs n p) (Abs _ v) = match r gamma (ExtendTel dummyDom (Abs n k)) p v
  match r gamma k (Abs n p) (NoAbs _ v) = match r gamma (ExtendTel dummyDom (Abs n k)) p (raise 1 v)
  match r gamma k (NoAbs n p) (Abs _ v) = match r gamma (ExtendTel dummyDom (Abs n k)) (raise 1 p) v
  match r gamma k (NoAbs _ p) (NoAbs _ v) = match r gamma k p v

instance Match NLPat Level where
  match r gamma k p l = match r gamma k p =<< liftRed (reallyUnLevelView l)

instance Match NLPat Term where
  match r gamma k p v = do
    vb <- liftRed $ reduceB' v
    let n = size k
        b = void vb
        v = ignoreBlocking vb
        prettyPat  = addContext (gamma `abstract` k) (prettyTCM p)
        prettyTerm = addContext k (prettyTCM v)
    traceSDoc "rewriting" 100 (sep
      [ text "matching" <+> prettyPat
      , text "with" <+> prettyTerm]) $ do
    let yes = return ()
        no msg = do
          traceSDoc "rewriting" 80 (sep
            [ text "mismatch between" <+> prettyPat
            , text " and " <+> prettyTerm
            , msg ]) $ do
          matchingBlocked b
        block b' = do
          traceSDoc "rewriting" 80 (sep
            [ text "matching blocked on meta"
            , text (show b) ]) $ do
          matchingBlocked (b `mappend` b')
    case p of
      PWild  -> yes
      PVar i bvs -> do
        let allowedVars :: IntSet
            allowedVars = IntSet.fromList (map unArg bvs)
            isBadVar :: Int -> Bool
            isBadVar i = i < n && not (i `IntSet.member` allowedVars)
            perm :: Permutation
            perm = Perm n $ reverse $ map unArg $ bvs
            tel :: Telescope
            tel = permuteTel perm k
        ok <- liftRed $ reallyFree isBadVar v
        case ok of
          Left b         -> block b
          Right Nothing  -> no (text "")
          Right (Just v) -> tellSub r (i-n) $ teleLam tel $ renameP __IMPOSSIBLE__ perm v
      PDef f ps -> do
        v <- liftRed $ constructorForm =<< unLevel v
        case ignoreSharing v of
          Def f' es
            | f == f'   -> match r gamma k ps es
          Con c _ vs
            | f == conName c -> match r gamma k ps (Apply <$> vs)
            | otherwise -> do -- @c@ may be a record constructor
                mr <- liftRed $ isRecordConstructor (conName c)
                case mr of
                  Just (_, def) | recEtaEquality def -> do
                    let fs = recFields def
                        qs = map (fmap $ \f -> PDef f (ps ++ [Proj ProjSystem f])) fs
                    match r gamma k qs vs
                  _ -> no (text "")
          Lam i u -> do
            let pbody = PDef f (raise 1 ps ++ [Apply $ Arg i $ PTerm (var 0)])
                body  = absBody u
            match r gamma (ExtendTel dummyDom (Abs (absName u) k)) pbody body
          MetaV m es -> do
            matchingBlocked $ Blocked m ()
          v' -> do -- @f@ may be a record constructor as well
            mr <- liftRed $ isRecordConstructor f
            case mr of
              Just (_, def) | recEtaEquality def -> do
                let fs  = recFields def
                    ws  = map (fmap $ \f -> v `applyE` [Proj ProjSystem f]) fs
                    qs = fromMaybe __IMPOSSIBLE__ $ allApplyElims ps
                match r gamma k qs ws
              _ -> no (text "")
      PLam i p' -> do
        let body = Abs (absName p') $ raise 1 v `apply` [Arg i (var 0)]
        match r gamma k p' body
      PPi pa pb  -> case ignoreSharing v of
        Pi a b -> match r gamma k pa a >> match r gamma k pb b
        MetaV m es -> matchingBlocked $ Blocked m ()
        _ -> no (text "")
      PBoundVar i ps -> case ignoreSharing v of
        Var i' es | i == i' -> match r gamma k ps es
        Con c _ vs -> do -- @c@ may be a record constructor
          mr <- liftRed $ isRecordConstructor (conName c)
          case mr of
            Just (_, def) | recEtaEquality def -> do
              let fs = recFields def
                  qs = map (fmap $ \f -> PBoundVar i (ps ++ [Proj ProjSystem f])) fs
              match r gamma k qs vs
            _ -> no (text "")
        Lam info u -> do
          let pbody = PBoundVar i (raise 1 ps ++ [Apply $ Arg info $ PTerm (var 0)])
              body  = absBody u
          match r gamma (ExtendTel dummyDom (Abs (absName u) k)) pbody body
        MetaV m es -> matchingBlocked $ Blocked m ()
        _ -> no (text "")
      PTerm u -> tellEq gamma k u v

-- Checks if the given term contains any free variables that satisfy the
-- given condition on their DBI, possibly normalizing the term in the process.
-- Returns `Right Nothing` if there are such variables, `Right (Just v')`
-- if there are none (where v' is the possibly normalized version of the given
-- term) or `Left b` if the problem is blocked on a meta.
reallyFree :: (Reduce a, Normalise a, Free a)
           => (Int -> Bool) -> a -> ReduceM (Either Blocked_ (Maybe a))
reallyFree f v = do
    let xs = getVars v
    if null (stronglyRigidVars xs) && null (unguardedVars xs)
    then do
      if null (weaklyRigidVars xs) && null (flexibleVars xs)
         && null (irrelevantVars xs)
      then return $ Right $ Just v
      else do
        bv <- normaliseB' v
        let b  = void bv
            v  = ignoreBlocking bv
            xs = getVars v
            b' = foldMap (foldMap $ \m -> Blocked m ()) $ flexibleVars xs
        if null (stronglyRigidVars xs) && null (unguardedVars xs)
           && null (weaklyRigidVars xs) && null (irrelevantVars xs)
        then if null (flexibleVars xs)
             then return $ Right $ Just v
             else return $ Left $ b `mappend` b'
        else return $ Right Nothing
    else return $ Right Nothing
  where
    getVars v = runFree (\ i -> if f i then singleton i else empty) IgnoreNot v

makeSubstitution :: Telescope -> Sub -> Substitution
makeSubstitution gamma sub =
  prependS __IMPOSSIBLE__ (map val [0 .. size gamma-1]) IdS
    where
      val i = case IntMap.lookup i sub of
                Just (Irrelevant, v) -> Just $ dontCare v
                Just (_         , v) -> Just v
                Nothing              -> Nothing

checkPostponedEquations :: Substitution -> PostponedEquations -> ReduceM (Maybe Blocked_)
checkPostponedEquations sub eqs = forM' eqs $
  \ (PostponedEquation k lhs rhs) -> do
      let lhs' = applySubst (liftS (size k) sub) lhs
      traceSDoc "rewriting" 60 (sep
        [ text "checking postponed equality between" , addContext k (prettyTCM lhs')
        , text " and " , addContext k (prettyTCM rhs) ]) $ do
      equal lhs' rhs

-- main function
nonLinMatch :: (Match a b) => Telescope -> a -> b -> ReduceM (Either Blocked_ Substitution)
nonLinMatch gamma p v = do
  let no msg b = traceSDoc "rewriting" 80 (sep
                   [ text "matching failed during" <+> text msg
                   , text "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ match Relevant gamma EmptyTel p v) (no "matching") $ \ s -> do
    let sub = makeSubstitution gamma $ s^.nlmSub
        eqs = s^.nlmEqs
    traceSDoc "rewriting" 90 (text $ "sub = " ++ show sub) $ do
    ok <- checkPostponedEquations sub eqs
    case ok of
      Nothing -> return $ Right sub
      Just b  -> no "checking of postponed equations" b

-- | Untyped βη-equality, does not handle things like empty record types.
--   Returns `Nothing` if the terms are equal, or `Just b` if the terms are not
--   (where b contains information about possible metas blocking the comparison)

-- TODO: implement a type-directed, lazy version of this function.
equal :: Term -> Term -> ReduceM (Maybe Blocked_)
equal u v = do
  (u, v) <- etaContract =<< normalise' (u, v)
  let ok    = u == v
      metas = allMetas (u, v)
      block = caseMaybe (headMaybe metas)
                (NotBlocked ReallyNotBlocked ())
                (\m -> Blocked m ())
  if ok then return Nothing else do
    traceSDoc "rewriting" 80 (sep
      [ text "mismatch between " <+> prettyTCM u
      , text " and " <+> prettyTCM v
      ]) $ do
    return $ Just block

-- | Normalise the given term but also preserve blocking tags
--   TODO: implement a more efficient version of this.
normaliseB' :: (Reduce t, Normalise t) => t -> ReduceM (Blocked t)
normaliseB' = normalise' >=> reduceB'
