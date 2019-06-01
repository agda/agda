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
import Data.Monoid
import Data.Traversable (Traversable,traverse)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Common
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Internal

import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Irrelevance (workOnTypes)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (HasBuiltins(..), getBuiltin', builtinLevel, primLevelSuc, primLevelMax)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
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

import Agda.Utils.Impossible

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

-- | Add substitution @i |-> v : a@ to result of matching.
tellSub :: Relevance -> Int -> Type -> Term -> NLM ()
tellSub r i a v = do
  old <- IntMap.lookup i <$> use nlmSub
  case old of
    Nothing -> nlmSub %= IntMap.insert i (r,v)
    Just (r',v')
      | isIrrelevant r  -> return ()
      | isIrrelevant r' -> nlmSub %= IntMap.insert i (r,v)
      | otherwise       -> whenJustM (equal a v v') matchingBlocked

tellEq :: Telescope -> Telescope -> Type -> Term -> Term -> NLM ()
tellEq gamma k a u v = do
  traceSDoc "rewriting.match" 30 (sep
               [ "adding equality between" <+> addContext (gamma `abstract` k) (prettyTCM u)
               , " and " <+> addContext k (prettyTCM v) ]) $ do
  nlmEqs %= (PostponedEquation k a u v:)

type Sub = IntMap (Relevance, Term)

-- | Matching against a term produces a constraint
--   which we have to verify after applying
--   the substitution computed by matching.
data PostponedEquation = PostponedEquation
  { eqFreeVars :: Telescope -- ^ Telescope of free variables in the equation
  , eqType :: Type    -- ^ Type of the equation, living in same context as the rhs.
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
      ~(Pi a b) <- unEl <$> reduce t
      match r gamma k a p v
      t' <- addContext k $ t `piApplyM` v
      let hd' = hd `apply` [ v ]
      match r gamma k (t',hd') ps vs

    (Proj o f, Proj o' f') | f == f' -> do
      ~(Just (El _ (Pi a b))) <- getDefType f =<< reduce t
      let t' = b `absApp` hd
      hd' <- addContext k $ applyDef o f (argFromDom a $> hd)
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
  match r gamma k t p v = match r gamma k t (unDom p) (unDom v)

instance Match () NLPType Type where
  match r gamma k _ (NLPType lp p) (El s a) = workOnTypes $ do
    match r gamma k () lp s
    match r gamma k (sort s) p a

-- We mine sort annotations for solutions to pattern variables of type
-- Level, but a wrong sort can never block reduction.
instance Match () NLPat Sort where
  match r gamma k _ p s = case s of
    Type l -> match Irrelevant gamma k () p l
    _      -> return ()

instance Match () NLPat Level where
  match r gamma k _ p l = do
    t <- El (mkType 0) . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    v <- reallyUnLevelView l
    match r gamma k t p v

instance Match Type NLPat Term where
  match r gamma k t p v = do
    vbt <- addContext k $ reduceB (v,t)
    etaRecord <- addContext k $ isEtaRecordType t
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
        no msg = if r == Irrelevant then yes else do
          traceSDoc "rewriting.match" 10 (sep
            [ "mismatch between" <+> prettyPat
            , " and " <+> prettyTerm
            , " of type " <+> prettyType
            , msg ]) $ do
          traceSDoc "rewriting.match" 30 (sep
            [ "blocking tag from reduction: " <+> text (show b) ]) $ do
          matchingBlocked b
        block b' = if r == Irrelevant then yes else do
          traceSDoc "rewriting.match" 10 (sep
            [ "matching blocked on meta"
            , text (show b') ]) $ do
          traceSDoc "rewriting.match" 30 (sep
            [ "blocking tag from reduction: " <+> text (show b') ]) $ do
          matchingBlocked (b `mappend` b')
    case p of
      PVar i bvs -> traceSDoc "rewriting.match" 60 ("matching a PVar: " <+> text (show i)) $ do
        let allowedVars :: IntSet
            allowedVars = IntSet.fromList (map unArg bvs)
            badVars :: IntSet
            badVars = IntSet.difference (IntSet.fromList (downFrom n)) allowedVars
            perm :: Permutation
            perm = Perm n $ reverse $ map unArg $ bvs
            tel :: Telescope
            tel = permuteTel perm k
        ok <- addContext k $ reallyFree badVars v
        case ok of
          Left b         -> block b
          Right Nothing  -> no ""
          Right (Just v) -> tellSub r (i-n) t $ teleLam tel $ renameP __IMPOSSIBLE__ perm v
      _ | MetaV m es <- v -> matchingBlocked $ Blocked m ()

      PDef f ps -> traceSDoc "rewriting.match" 60 ("matching a PDef: " <+> prettyTCM f) $ do
        v <- addContext k $ constructorForm =<< unLevel v
        case v of
          Def f' es
            | f == f'   -> do
                ft <- addContext k $ defType <$> getConstInfo f
                match r gamma k (ft , Def f []) ps es
          Con c ci vs
            | f == conName c -> do
                ~(Just (_ , ct)) <- addContext k $ getFullyAppliedConType c t
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
            def <- addContext k $ theDef <$> getConstInfo d
            (tel, c, ci, vs) <- addContext k $ etaExpandRecord_ d pars def v
            ~(Just (_ , ct)) <- addContext k $ getFullyAppliedConType c t
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
          def <- addContext k $ theDef <$> getConstInfo d
          (tel, c, ci, vs) <- addContext k $ etaExpandRecord_ d pars def v
          ~(Just (_ , ct)) <- addContext k $ getFullyAppliedConType c t
          let flds = recFields def
              ps'  = map (fmap $ \fld -> PBoundVar i (ps ++ [Proj ProjSystem fld])) flds
          match r gamma k (ct, Con c ci []) (map Apply ps') (map Apply vs)
        _ -> no ""
      PTerm u -> traceSDoc "rewriting.match" 60 ("matching a PTerm" <+> addContext (gamma `abstract` k) (prettyTCM u)) $
        tellEq gamma k t u v

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

checkPostponedEquations :: (MonadReduce m, MonadAddContext m, HasConstInfo m, HasBuiltins m, MonadDebug m)
                        => Substitution -> PostponedEquations -> m (Maybe Blocked_)
checkPostponedEquations sub eqs = forM' eqs $
  \ (PostponedEquation k a lhs rhs) -> do
      let lhs' = applySubst (liftS (size k) sub) lhs
      traceSDoc "rewriting.match" 30 (sep
        [ "checking postponed equality between" , addContext k (prettyTCM lhs')
        , " and " , addContext k (prettyTCM rhs) ]) $ do
      addContext k $ equal a lhs' rhs

-- main function
nonLinMatch :: (MonadReduce m, MonadAddContext m, HasConstInfo m, HasBuiltins m, MonadDebug m, Match t a b)
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

-- | Typed βη-equality, also handles empty record types.
--   Returns `Nothing` if the terms are equal, or `Just b` if the terms are not
--   (where b contains information about possible metas blocking the comparison)
equal :: (MonadReduce m, MonadAddContext m, HasConstInfo m, HasBuiltins m)
      => Type -> Term -> Term -> m (Maybe Blocked_)
equal a u v = pureEqualTerm a u v >>= \case
  True -> return Nothing
  False -> traceSDoc "rewriting.match" 10 (sep
      [ "mismatch between " <+> prettyTCM u
      , " and " <+> prettyTCM v
      ]) $ do
    return $ Just block

  where
    block = caseMaybe (firstMeta (u, v))
              (NotBlocked ReallyNotBlocked ())
              (\m -> Blocked m ())
