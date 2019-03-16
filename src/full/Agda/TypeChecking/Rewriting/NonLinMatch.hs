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

import Data.Maybe
import Data.Traversable (Traversable,traverse)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Common
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Internal

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (getBuiltin', builtinLevel, primLevelSuc, primLevelMax)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as Red
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

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
--   The third argument is the type of the term.

class PatternFrom t a b where
  patternFrom :: Relevance -> Int -> t -> a -> TCM b

instance (PatternFrom t a b) => PatternFrom (Dom t) (Arg a) (Arg b) where
  patternFrom r k t u = let r' = r `composeRelevance` getRelevance u
                        in  traverse (patternFrom r' k $ unDom t) u

instance PatternFrom (Type, Term) Elims [Elim' NLPat] where
  patternFrom r k (t,hd) = \case
    [] -> return []
    (Apply u : es) -> do
      ~(Pi a b) <- reduce $ unEl t
      p   <- patternFrom r k a u
      t'  <- t `piApplyM` u
      let hd' = hd `apply` [ u ]
      ps  <- patternFrom r k (t',hd') es
      return $ Apply p : ps
    (IApply x y u : es) -> __IMPOSSIBLE__ -- TODO
    (Proj o f : es) -> do
      ~(Just (El _ (Pi a b))) <- getDefType f =<< reduce t
      let t' = b `absApp` hd
      hd' <- applyDef o f (argFromDom a $> hd)
      ps  <- patternFrom r k (t',hd') es
      return $ Proj o f : ps

instance (PatternFrom t a b) => PatternFrom t (Dom a) (Dom b) where
  patternFrom r k t = traverse $ patternFrom r k t

instance PatternFrom () Type NLPType where
  patternFrom r k _ a = NLPType <$> patternFrom r k () (getSort a)
                                <*> patternFrom r k (sort $ getSort a) (unEl a)

instance PatternFrom () Sort NLPat where
  patternFrom r k _ s = do
    s <- reduce s
    let done = return PWild
    case s of
      Type l   -> do
        t <- levelType
        patternFrom Irrelevant k t (Level l)
      Prop l   -> done --TODO
      Inf      -> done
      SizeUniv -> done
      PiSort _ _ -> __IMPOSSIBLE__
      UnivSort _ -> __IMPOSSIBLE__
      MetaS{}  -> __IMPOSSIBLE__
      DefS{}   -> done
      DummyS s -> do
        reportSLn "impossible" 10 $ unlines
          [ "patternFrom: hit dummy sort with content:"
          , s
          ]
        __IMPOSSIBLE__

instance PatternFrom Type Term NLPat where
  patternFrom r k t v = do
    t <- reduce t
    etaRecord <- isEtaRecordType t
    v <- unLevel =<< reduce v
    reportSDoc "rewriting.build" 60 $ sep
      [ "building a pattern from term v = " <+> prettyTCM v
      , " of type " <+> prettyTCM t
      ]
    let done = if isIrrelevant r then
                 return PWild
               else
                 return $ PTerm v
    case (unEl t , v) of
      (Pi a b , _) -> do
        let body = raise 1 v `apply` [ Arg (domInfo a) $ var 0 ]
        p <- addContext a (patternFrom r (k+1) (absBody b) body)
        return $ PLam (domInfo a) $ Abs (absName b) p
      (_ , Var i es)
       | i < k     -> do
           t <- typeOfBV i
           PBoundVar i <$> patternFrom r k (t , var i) es
       -- The arguments of `var i` should be distinct bound variables
       -- in order to build a Miller pattern
       | Just vs <- allApplyElims es -> do
           TelV tel _ <- telView =<< typeOfBV i
           unless (size tel >= size vs) __IMPOSSIBLE__
           let ts = applySubst (parallelS $ reverse $ map unArg vs) $ map unDom $ flattenTel tel
           mbvs <- forM (zip ts vs) $ \(t , v) -> do
             isEtaVar (unArg v) t >>= \case
               Just j | j < k -> return $ Just $ v $> j
               _              -> return Nothing
           case sequence mbvs of
             Just bvs | fastDistinct bvs -> do
               let allBoundVars = IntSet.fromList (downFrom k)
                   ok = not (isIrrelevant r) ||
                        IntSet.fromList (map unArg bvs) == allBoundVars
               if ok then return (PVar i bvs) else done
             _ -> done
       | otherwise -> done
      (_ , _ ) | Just (d, pars) <- etaRecord -> do
        def <- theDef <$> getConstInfo d
        (tel, c, ci, vs) <- etaExpandRecord_ d pars def v
        caseMaybeM (getFullyAppliedConType c t) __IMPOSSIBLE__ $ \ (_ , ct) -> do
        PDef (conName c) <$> patternFrom r k (ct , Con c ci []) (map Apply vs)
      (_ , Lam i t) -> __IMPOSSIBLE__
      (_ , Lit{})   -> done
      (_ , Def f es) | isIrrelevant r -> done
      (_ , Def f es) -> do
        Def lsuc [] <- primLevelSuc
        Def lmax [] <- primLevelMax
        case es of
          [x]     | f == lsuc -> done
          [x , y] | f == lmax -> done
          _                   -> do
            ft <- defType <$> getConstInfo f
            PDef f <$> patternFrom r k (ft , Def f []) es
      (_ , Con c ci vs) | isIrrelevant r -> done
      (_ , Con c ci vs) ->
        caseMaybeM (getFullyAppliedConType c t) __IMPOSSIBLE__ $ \ (_ , ct) -> do
        PDef (conName c) <$> patternFrom r k (ct , Con c ci []) vs
      (_ , Pi a b) | isIrrelevant r -> done
      (_ , Pi a b) -> do
        pa <- patternFrom r k () a
        pb <- addContext a (patternFrom r (k+1) () $ absBody b)
        return $ PPi pa (Abs (absName b) pb)
      (_ , Sort s)     -> done
      (_ , Level l)    -> __IMPOSSIBLE__
      (_ , DontCare{}) -> return PWild
      (_ , MetaV{})    -> __IMPOSSIBLE__
      (_ , Dummy s)    -> __IMPOSSIBLE_VERBOSE__ s

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

runNLM :: (MonadReduce m) => NLM () -> m (Either Blocked_ NLMState)
runNLM nlm = do
  (ok,out) <- liftReduce $ runStateT (runExceptT nlm) empty
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
      | otherwise       -> whenJustM (equal v v') matchingBlocked

tellEq :: Telescope -> Telescope -> Term -> Term -> NLM ()
tellEq gamma k u v = do
  traceSDoc "rewriting.match" 30 (sep
               [ "adding equality between" <+> addContext (gamma `abstract` k) (prettyTCM u)
               , " and " <+> addContext k (prettyTCM v) ]) $ do
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

class Match t a b where
  match :: Relevance  -- ^ Are we currently matching in an irrelevant context?
        -> Telescope  -- ^ The telescope of pattern variables
        -> Telescope  -- ^ The telescope of lambda-bound variables
        -> t          -- ^ The type of the pattern
        -> a          -- ^ The pattern to match
        -> b          -- ^ The term to be matched against the pattern
        -> NLM ()

instance Match t a b => Match (Dom t) (Arg a) (Arg b) where
  match r gamma k t p v = let r' = r `composeRelevance` getRelevance p
                          in  match r' gamma k (unDom t) (unArg p) (unArg v)

instance Match (Type, Term) [Elim' NLPat] Elims where
  match r gamma k (t, hd) [] [] = return ()
  match r gamma k (t, hd) [] _  = matchingBlocked $ NotBlocked ReallyNotBlocked ()
  match r gamma k (t, hd) _  [] = matchingBlocked $ NotBlocked ReallyNotBlocked ()
  match r gamma k (t, hd) (p:ps) (v:vs) = case (p,v) of
    (Apply p, Apply v) -> do
      ~(Pi a b) <- reduce $ unEl t
      match r gamma k a p v
      t' <- Red.addCtxTel k $ t `piApplyM` v
      let hd' = hd `apply` [ v ]
      match r gamma k (t',hd') ps vs

    (Proj o f, Proj o' f') | f == f' -> do
      ~(Just (El _ (Pi a b))) <- getDefType f =<< reduce t
      let t' = b `absApp` hd
      hd' <- Red.addCtxTel k $ applyDef o f (argFromDom a $> hd)
      match r gamma k (t',hd') ps vs

    (Proj _ f, Proj _ f') | otherwise -> do
      traceSDoc "rewriting.match" 20 (sep
        [ "mismatch between projections " <+> prettyTCM f
        , " and " <+> prettyTCM f' ]) mzero

    (Apply{}, Proj{} ) -> __IMPOSSIBLE__
    (Proj{} , Apply{}) -> __IMPOSSIBLE__

    (IApply{} , _    ) -> __IMPOSSIBLE__ -- TODO
    (_ , IApply{}    ) -> __IMPOSSIBLE__ -- TODO

instance Match t a b => Match t (Dom a) (Dom b) where
  match r gamma k t p v = match r gamma k t (C.unDom p) (C.unDom v)

instance Match () NLPType Type where
  match r gamma k _ (NLPType lp p) (El s a) = do
    match r gamma k () lp s
    match r gamma k (sort s) p a

instance Match () NLPat Sort where
  match r gamma k _ p s = case (p , s) of
    (PWild , _     ) -> return ()
    (p     , Type l) -> match Irrelevant gamma k () p l
    _                -> matchingBlocked $ NotBlocked ReallyNotBlocked ()

instance Match () NLPat Level where
  match r gamma k _ p l = do
    t <- El (mkType 0) . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    v <- reallyUnLevelView l
    match r gamma k t p v

instance Match Type NLPat Term where
  match r gamma k t p v = do
    vbt <- Red.addCtxTel k $ reduceB (v,t)
    etaRecord <- Red.addCtxTel k $ isEtaRecordType t
    let n = size k
        b = void vbt
        (v,t) = ignoreBlocking vbt
        prettyPat  = withShowAllArguments $ addContext (gamma `abstract` k) (prettyTCM p)
        prettyTerm = withShowAllArguments $ addContext k $ prettyTCM v
        prettyType = withShowAllArguments $ addContext k $ prettyTCM t
    traceSDoc "rewriting.match" 30 (sep
      [ "matching pattern " <+> prettyPat
      , "  with term      " <+> prettyTerm
      , "  of type        " <+> prettyType ]) $ do
    traceSDoc "rewriting.match" 80 (vcat
      [ "  raw pattern:  " <+> text (show p)
      , "  raw term:     " <+> text (show v)
      , "  raw type:     " <+> text (show t) ]) $ do
    traceSDoc "rewriting.match" 70 (vcat
      [ "pattern vars:   " <+> prettyTCM gamma
      , "bound vars:     " <+> prettyTCM k ]) $ do
    let yes = return ()
        no msg = do
          traceSDoc "rewriting.match" 10 (sep
            [ "mismatch between" <+> prettyPat
            , " and " <+> prettyTerm
            , " of type " <+> prettyType
            , msg ]) $ do
          traceSDoc "rewriting.match" 30 (sep
            [ "blocking tag from reduction: " <+> text (show b) ]) $ do
          matchingBlocked b
        block b' = do
          traceSDoc "rewriting.match" 10 (sep
            [ "matching blocked on meta"
            , text (show b') ]) $ do
          traceSDoc "rewriting.match" 30 (sep
            [ "blocking tag from reduction: " <+> text (show b') ]) $ do
          matchingBlocked (b `mappend` b')
    case p of
      PWild  -> yes
      PVar i bvs -> traceSDoc "rewriting.match" 60 ("matching a PVar: " <+> text (show i)) $ do
        let allowedVars :: IntSet
            allowedVars = IntSet.fromList (map unArg bvs)
            badVars :: IntSet
            badVars = IntSet.difference (IntSet.fromList (downFrom n)) allowedVars
            perm :: Permutation
            perm = Perm n $ reverse $ map unArg $ bvs
            tel :: Telescope
            tel = permuteTel perm k
        ok <- Red.addCtxTel k $ reallyFree badVars v
        case ok of
          Left b         -> block b
          Right Nothing  -> no ""
          Right (Just v) -> tellSub r (i-n) $ teleLam tel $ renameP __IMPOSSIBLE__ perm v

      _ | MetaV m es <- v -> matchingBlocked $ Blocked m ()

      PDef f ps -> traceSDoc "rewriting.match" 60 ("matching a PDef: " <+> prettyTCM f) $ do
        v <- Red.addCtxTel k $ constructorForm =<< unLevel v
        case v of
          Def f' es
            | f == f'   -> do
                ft <- Red.addCtxTel k $ defType <$> getConstInfo f
                match r gamma k (ft , Def f []) ps es
          Con c ci vs
            | f == conName c -> do
                ~(Just (_ , ct)) <- Red.addCtxTel k $ getFullyAppliedConType c t
                match r gamma k (ct , Con c ci []) ps vs
          _ | Pi a b <- unEl t -> do
            let ai    = domInfo a
                pbody = PDef f $ raise 1 ps ++ [ Apply $ Arg ai $ PTerm $ var 0 ]
                body  = raise 1 v `apply` [ Arg (domInfo a) $ var 0 ]
                k'    = ExtendTel a (Abs (absName b) k)
            match r gamma k' (absBody b) pbody body
          _ | Just (d, pars) <- etaRecord -> do
          -- If v is not of record constructor form but we are matching at record
          -- type, e.g., we eta-expand both v to (c vs) and
          -- the pattern (p = PDef f ps) to @c (p .f1) ... (p .fn)@.
            def <- Red.addCtxTel k $ theDef <$> getConstInfo d
            (tel, c, ci, vs) <- Red.addCtxTel k $ etaExpandRecord_ d pars def v
            ~(Just (_ , ct)) <- Red.addCtxTel k $ getFullyAppliedConType c t
            let flds = recFields def
                mkField fld = PDef f (ps ++ [Proj ProjSystem fld])
                -- Issue #3335: when matching against the record constructor,
                -- don't add projections but take record field directly.
                ps'
                  | conName c == f = ps
                  | otherwise      = map (Apply . fmap mkField) flds
            match r gamma k (ct, Con c ci []) ps' (map Apply vs)
          MetaV m es -> do
            matchingBlocked $ Blocked m ()
          _  -> no ""
      PLam i p' -> case unEl t of
        Pi a b -> do
          let body = raise 1 v `apply` [Arg i (var 0)]
              k'   = ExtendTel a (Abs (absName b) k)
          match r gamma k' (absBody b) (absBody p') body
        _ -> no ""
      PPi pa pb -> case v of
        Pi a b -> do
          match r gamma k () pa a
          let k' = ExtendTel a (Abs (absName b) k)
          match r gamma k' () (absBody pb) (absBody b)
        _ -> no ""
      PBoundVar i ps -> case v of
        Var i' es | i == i' -> do
          let ti = unDom $ indexWithDefault __IMPOSSIBLE__ (flattenTel k) i
          match r gamma k (ti , var i) ps es
        _ | Pi a b <- unEl t -> do
          let ai    = domInfo a
              pbody = PBoundVar i $ raise 1 ps ++ [ Apply $ Arg ai $ PTerm $ var 0 ]
              body  = raise 1 v `apply` [ Arg ai $ var 0 ]
              k'    = ExtendTel a (Abs (absName b) k)
          match r gamma k' (absBody b) pbody body
        _ | Just (d, pars) <- etaRecord -> do
          def <- Red.addCtxTel k $ theDef <$> getConstInfo d
          (tel, c, ci, vs) <- Red.addCtxTel k $ etaExpandRecord_ d pars def v
          ~(Just (_ , ct)) <- Red.addCtxTel k $ getFullyAppliedConType c t
          let flds = recFields def
              ps'  = map (fmap $ \fld -> PBoundVar i (ps ++ [Proj ProjSystem fld])) flds
          match r gamma k (ct, Con c ci []) (map Apply ps') (map Apply vs)
        _ -> no ""
      PTerm u -> traceSDoc "rewriting.match" 60 ("matching a PTerm" <+> addContext (gamma `abstract` k) (prettyTCM u)) $
        tellEq gamma k u v

-- Checks if the given term contains any free variables that satisfy the
-- given condition on their DBI, possibly reducing the term in the process.
-- Returns `Right Nothing` if there are such variables, `Right (Just v')`
-- if there are none (where v' is the possibly reduced version of the given
-- term) or `Left b` if the problem is blocked on a meta.
reallyFree :: (MonadReduce m, Reduce a, ForceNotFree a)
           => IntSet -> a -> m (Either Blocked_ (Maybe a))
reallyFree xs v = do
  (mxs , v') <- forceNotFree xs v
  case IntMap.foldr pickFree NotFree mxs of
    MaybeFree ms
      | null ms   -> return $ Right Nothing
      | otherwise -> return $ Left $
        Set.foldr (\m -> mappend $ Blocked m ()) (notBlocked ()) ms
    NotFree -> return $ Right (Just v')

  where
    -- Check if any of the variables occur freely.
    -- Prefer occurrences that do not depend on any metas.
    pickFree :: IsFree -> IsFree -> IsFree
    pickFree f1@(MaybeFree ms1) f2
      | null ms1  = f1
    pickFree f1@(MaybeFree ms1) f2@(MaybeFree ms2)
      | null ms2  = f2
      | otherwise = f1
    pickFree f1@(MaybeFree ms1) NotFree = f1
    pickFree NotFree f2 = f2


makeSubstitution :: Telescope -> Sub -> Substitution
makeSubstitution gamma sub =
  prependS __IMPOSSIBLE__ (map val [0 .. size gamma-1]) IdS
    where
      val i = case IntMap.lookup i sub of
                Just (Irrelevant, v) -> Just $ dontCare v
                Just (_         , v) -> Just v
                Nothing              -> Nothing

checkPostponedEquations :: (MonadReduce m, HasConstInfo m, MonadDebug m)
                        => Substitution -> PostponedEquations -> m (Maybe Blocked_)
checkPostponedEquations sub eqs = forM' eqs $
  \ (PostponedEquation k lhs rhs) -> do
      let lhs' = applySubst (liftS (size k) sub) lhs
      traceSDoc "rewriting.match" 30 (sep
        [ "checking postponed equality between" , addContext k (prettyTCM lhs')
        , " and " , addContext k (prettyTCM rhs) ]) $ do
      Red.addCtxTel k $ equal lhs' rhs

-- main function
nonLinMatch :: (MonadReduce m, HasConstInfo m, MonadDebug m, Match t a b)
            => Telescope -> t -> a -> b -> m (Either Blocked_ Substitution)
nonLinMatch gamma t p v = do
  let no msg b = traceSDoc "rewriting.match" 10 (sep
                   [ "matching failed during" <+> text msg
                   , "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ match Relevant gamma EmptyTel t p v) (no "matching") $ \ s -> do
    let sub = makeSubstitution gamma $ s^.nlmSub
        eqs = s^.nlmEqs
    traceSDoc "rewriting.match" 90 (text $ "sub = " ++ show sub) $ do
    ok <- checkPostponedEquations sub eqs
    case ok of
      Nothing -> return $ Right sub
      Just b  -> no "checking of postponed equations" b

-- | Untyped βη-equality, does not handle things like empty record types.
--   Returns `Nothing` if the terms are equal, or `Just b` if the terms are not
--   (where b contains information about possible metas blocking the comparison)

-- TODO: implement a type-directed, lazy version of this function.
equal :: (MonadReduce m, HasConstInfo m)
      => Term -> Term -> m (Maybe Blocked_)
equal u v = do
  (u, v) <- etaContract =<< normalise (u, v)
  let ok    = u == v
      metas = allMetas (u, v)
      block = caseMaybe (headMaybe metas)
                (NotBlocked ReallyNotBlocked ())
                (\m -> Blocked m ())
  if ok then return Nothing else do
    traceSDoc "rewriting.match" 10 (sep
      [ "mismatch between " <+> prettyTCM u
      , " and " <+> prettyTCM v
      ]) $ do
    return $ Just block
