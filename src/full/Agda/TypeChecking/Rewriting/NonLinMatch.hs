{-# LANGUAGE NondecreasingIndentation #-}

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

import Control.Applicative  ( Alternative )
import Control.Monad        ( void )
import Control.Monad.Except ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.State  ( MonadState, StateT, runStateT )

import qualified Control.Monad.Fail as Fail

import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Irrelevance (isPropM)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad hiding (constructorForm)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Primitive.Cubical.Base

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size

import Agda.Utils.Impossible


-- | Monad for non-linear matching.
newtype NLM a = NLM { unNLM :: ExceptT Blocked_ (StateT NLMState ReduceM) a }
  deriving ( Functor, Applicative, Monad, Fail.MonadFail
           , Alternative, MonadPlus
           , MonadError Blocked_, MonadState NLMState
           , HasBuiltins, HasConstInfo, HasOptions, ReadTCState
           , MonadTCEnv, MonadReduce, MonadAddContext, MonadDebug
           , PureTCM
           )

instance MonadBlock NLM where
  patternViolation b = throwError $ Blocked b ()
  catchPatternErr h f = catchError f $ \case
    Blocked b _      -> h b
    err@NotBlocked{} -> throwError err

data NLMState = NLMState
  { _nlmSub   :: Sub
  , _nlmEqs   :: PostponedEquations
  }

instance Null NLMState where
  empty  = NLMState { _nlmSub = empty , _nlmEqs = empty }
  null s = null (s^.nlmSub) && null (s^.nlmEqs)

nlmSub :: Lens' NLMState Sub
nlmSub f s = f (_nlmSub s) <&> \x -> s {_nlmSub = x}

nlmEqs :: Lens' NLMState PostponedEquations
nlmEqs f s = f (_nlmEqs s) <&> \x -> s {_nlmEqs = x}

runNLM :: (MonadReduce m) => NLM () -> m (Either Blocked_ NLMState)
runNLM nlm = do
  (ok,out) <- liftReduce $ runStateT (runExceptT $ unNLM nlm) empty
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

class Match a b where
  match :: Relevance  -- ^ Are we currently matching in an irrelevant context?
        -> Telescope  -- ^ The telescope of pattern variables
        -> Telescope  -- ^ The telescope of lambda-bound variables
        -> TypeOf b   -- ^ The type of the pattern
        -> a          -- ^ The pattern to match
        -> b          -- ^ The term to be matched against the pattern
        -> NLM ()

instance Match a b => Match (Arg a) (Arg b) where
  match r gamma k t p v = let r' = r `composeRelevance` getRelevance p
                          in  match r' gamma k (unDom t) (unArg p) (unArg v)

instance Match [Elim' NLPat] Elims where
  match r gamma k (t, hd) [] [] = return ()
  match r gamma k (t, hd) [] _  = matchingBlocked $ NotBlocked ReallyNotBlocked ()
  match r gamma k (t, hd) _  [] = matchingBlocked $ NotBlocked ReallyNotBlocked ()
  match r gamma k (t, hd) (p:ps) (v:vs) =
   traceSDoc "rewriting.match" 50 (sep
     [ "matching elimination " <+> addContext (gamma `abstract` k) (prettyTCM p)
     , "  with               " <+> addContext k (prettyTCM v)
     , "  eliminating head   " <+> addContext k (prettyTCM $ hd []) <+> ":" <+> addContext k (prettyTCM t)]) $ do

   let no  = matchingBlocked $ NotBlocked ReallyNotBlocked ()
   case (p,v) of
    (Apply p, Apply v) -> (addContext k $ unEl <$> reduce t) >>= \case
      Pi a b -> do
        match r gamma k a p v
        let t'  = absApp b (unArg v)
            hd' = hd . (Apply v:)
        match r gamma k (t',hd') ps vs
      t -> traceSDoc "rewriting.match" 20
        ("application at non-pi type (possible non-confluence?) " <+> prettyTCM t) mzero

    (IApply x y p , IApply u v i) -> (addContext k $ pathView =<< reduce t) >>= \case
      PathType s q l b _u _v -> do
        Right interval <- runExceptT primIntervalType
        match r gamma k interval p i
        let t' = El s $ unArg b `apply` [ defaultArg i ]
        let hd' = hd . (IApply u v i:)
        match r gamma k (t',hd') ps vs
      t -> traceSDoc "rewriting.match" 20
        ("interval application at non-pi type (possible non-confluence?) " <+> prettyTCM (pathUnview t)) mzero

    (Proj o f, Proj o' f') | f == f' -> do
      addContext k (getDefType f =<< reduce t) >>= \case
        Just (El _ (Pi a b)) -> do
          let u = hd []
              t' = b `absApp` u
          hd' <- addContext k $ applyE <$> applyDef o f (argFromDom a $> u)
          match r gamma k (t',hd') ps vs
        _ -> no

    (Proj _ f, Proj _ f') | otherwise -> do
      traceSDoc "rewriting.match" 20 (sep
        [ "mismatch between projections " <+> prettyTCM f
        , " and " <+> prettyTCM f' ]) mzero

    (Apply{}, Proj{} ) -> no
    (Proj{} , Apply{}) -> no

    (IApply{} , _    ) -> __IMPOSSIBLE__ -- TODO
    (_ , IApply{}    ) -> __IMPOSSIBLE__ -- TODO

instance Match a b => Match (Dom a) (Dom b) where
  match r gamma k t p v = match r gamma k t (unDom p) (unDom v)

instance Match NLPType Type where
  match r gamma k _ (NLPType sp p) (El s a) = workOnTypes $ do
    match r gamma k () sp s
    match r gamma k (sort s) p a

instance Match NLPSort Sort where
  match r gamma k _ p s = do
    bs <- addContext k $ reduceB s
    let b = void bs
        s = ignoreBlocking bs
        yes = return ()
        no  = matchingBlocked $ NotBlocked ReallyNotBlocked ()
    traceSDoc "rewriting.match" 30 (sep
      [ "matching pattern " <+> addContext (gamma `abstract` k) (prettyTCM p)
      , "  with sort      " <+> addContext k (prettyTCM s) ]) $ do
    case (p , s) of
      (PUniv u lp    , Univ u' l) | u == u'          -> match r gamma k () lp l
      (PInf up np    , Inf u n)   | up == u, np == n -> yes
      (PSizeUniv     , SizeUniv)                     -> yes
      (PLockUniv     , LockUniv)                     -> yes
      (PLevelUniv    , LevelUniv)                    -> yes
      (PIntervalUniv , IntervalUniv)                 -> yes

      -- blocked cases
      (_ , UnivSort{}) -> matchingBlocked b
      (_ , PiSort{}  ) -> matchingBlocked b
      (_ , FunSort{} ) -> matchingBlocked b
      (_ , MetaS m _ ) -> matchingBlocked $ blocked_ m

      -- all other cases do not match
      (_ , _) -> no

instance Match NLPat Level where
  match r gamma k _ p l = do
    t <- El (mkType 0) . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    v <- reallyUnLevelView l
    match r gamma k t p v

instance Match NLPat Term where
  match r0 gamma k t p v = do
    vbt <- addContext k $ reduceB (v,t)
    let n = size k
        b = void vbt
        (v,t) = ignoreBlocking vbt
        prettyPat  = withShowAllArguments $ addContext (gamma `abstract` k) (prettyTCM p)
        prettyTerm = withShowAllArguments $ addContext k $ prettyTCM v
        prettyType = withShowAllArguments $ addContext k $ prettyTCM t
    etaRecord <- addContext k $ isEtaRecordType t
    pview <- pathViewAsPi'whnf
    prop <- fromRight __IMPOSSIBLE__ <.> runBlocked . addContext k $ isPropM t
    let r = if prop then Irrelevant else r0
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
        maybeBlock = \case
          MetaV m es -> matchingBlocked $ blocked_ m
          _          -> no ""
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
          Right (Just v) ->
            let t' = telePi  tel $ renameP impossible perm t
                v' = teleLam tel $ renameP impossible perm v
            in tellSub r (i-n) t' v'

      PDef f ps -> traceSDoc "rewriting.match" 60 ("matching a PDef: " <+> prettyTCM f) $ do
        v <- addContext k $ constructorForm =<< unLevel v
        case v of
          Def f' es
            | f == f'   -> do
                ft <- addContext k $ defType <$> getConstInfo f
                match r gamma k (ft , Def f) ps es
          Con c ci vs
            | f == conName c -> do
                addContext k (getFullyAppliedConType c t) >>= \case
                  Just (_ , ct) -> match r gamma k (ct , Con c ci) ps vs
                  Nothing -> no ""
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
            addContext k (getFullyAppliedConType c t) >>= \case
              Just (_ , ct) -> do
                let flds = map argFromDom $ recFields def
                    mkField fld = PDef f (ps ++ [Proj ProjSystem fld])
                    -- Issue #3335: when matching against the record constructor,
                    -- don't add projections but take record field directly.
                    ps'
                      | conName c == f = ps
                      | otherwise      = map (Apply . fmap mkField) flds
                match r gamma k (ct, Con c ci) ps' (map Apply vs)
              Nothing -> no ""
          v -> maybeBlock v
      PLam i p' -> case unEl t of
        Pi a b -> do
          let body = raise 1 v `apply` [Arg i (var 0)]
              k'   = ExtendTel a (Abs (absName b) k)
          match r gamma k' (absBody b) (absBody p') body
        _ | Left ((a,b),(x,y)) <- pview t -> do
          let body = raise 1 v `applyE` [ IApply (raise 1 x) (raise 1 y) $ var 0 ]
              k'   = ExtendTel a (Abs "i" k)
          match r gamma k' (absBody b) (absBody p') body
        v -> maybeBlock v
      PPi pa pb -> case v of
        Pi a b -> do
          match r gamma k () pa a
          let k' = ExtendTel a (Abs (absName b) k)
          match r gamma k' () (absBody pb) (absBody b)
        v -> maybeBlock v
      PSort ps -> case v of
        Sort s -> match r gamma k () ps s
        v -> maybeBlock v
      PBoundVar i ps -> case v of
        Var i' es | i == i' -> do
          let ti = unDom $ indexWithDefault __IMPOSSIBLE__ (flattenTel k) i
          match r gamma k (ti , Var i) ps es
        _ | Pi a b <- unEl t -> do
          let ai    = domInfo a
              pbody = PBoundVar (1+i) $ raise 1 ps ++ [ Apply $ Arg ai $ PTerm $ var 0 ]
              body  = raise 1 v `apply` [ Arg ai $ var 0 ]
              k'    = ExtendTel a (Abs (absName b) k)
          match r gamma k' (absBody b) pbody body
        _ | Just (d, pars) <- etaRecord -> do
          def <- addContext k $ theDef <$> getConstInfo d
          (tel, c, ci, vs) <- addContext k $ etaExpandRecord_ d pars def v
          addContext k (getFullyAppliedConType c t) >>= \case
            Just (_ , ct) -> do
              let flds = map argFromDom $ recFields def
                  ps'  = map (fmap $ \fld -> PBoundVar i (ps ++ [Proj ProjSystem fld])) flds
              match r gamma k (ct, Con c ci) (map Apply ps') (map Apply vs)
            Nothing -> no ""
        v -> maybeBlock v
      PTerm u -> traceSDoc "rewriting.match" 60 ("matching a PTerm" <+> addContext (gamma `abstract` k) (prettyTCM u)) $
        tellEq gamma k t u v

makeSubstitution :: Telescope -> Sub -> Maybe Substitution
makeSubstitution gamma sub =
  parallelS <$> traverse val [0 .. size gamma-1]
    where
      val i = case IntMap.lookup i sub of
                Just (Irrelevant, v) -> Just $ dontCare v
                Just (_         , v) -> Just v
                Nothing              -> Nothing

checkPostponedEquations :: PureTCM m
                        => Substitution -> PostponedEquations -> m (Maybe Blocked_)
checkPostponedEquations sub eqs = forM' eqs $
  \ (PostponedEquation k a lhs rhs) -> do
      let lhs' = applySubst (liftS (size k) sub) lhs
      traceSDoc "rewriting.match" 30 (sep
        [ "checking postponed equality between" , addContext k (prettyTCM lhs')
        , " and " , addContext k (prettyTCM rhs) ]) $ do
      addContext k $ equal a lhs' rhs

-- main function
nonLinMatch :: (PureTCM m, Match a b)
            => Telescope -> TypeOf b -> a -> b -> m (Either Blocked_ Substitution)
nonLinMatch gamma t p v = do
  let no msg b = traceSDoc "rewriting.match" 10 (sep
                   [ "matching failed during" <+> text msg
                   , "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ match Relevant gamma EmptyTel t p v) (no "matching") $ \ s -> do
    let msub = makeSubstitution gamma $ s^.nlmSub
        eqs = s^.nlmEqs
    traceSDoc "rewriting.match" 90 (text $ "msub = " ++ show msub) $ case msub of
      Nothing -> no "checking that all variables are bound" notBlocked_
      Just sub -> do
        ok <- checkPostponedEquations sub eqs
        case ok of
          Nothing -> return $ Right sub
          Just b  -> no "checking of postponed equations" b

-- | Typed βη-equality, also handles empty record types.
--   Returns `Nothing` if the terms are equal, or `Just b` if the terms are not
--   (where b contains information about possible metas blocking the comparison)
equal :: PureTCM m => Type -> Term -> Term -> m (Maybe Blocked_)
equal a u v = runBlocked (pureEqualTerm a u v) >>= \case
  Left b      -> return $ Just $ Blocked b ()
  Right True  -> return Nothing
  Right False -> traceSDoc "rewriting.match" 10 (sep
      [ "mismatch between " <+> prettyTCM u
      , " and " <+> prettyTCM v
      ]) $ do
    return $ Just $ NotBlocked ReallyNotBlocked ()

-- | Utility function for getting the name and type of a head term (i.e. a
--   `Def` or `Con` with no arguments)
getTypedHead :: PureTCM m => Term -> m (Maybe (QName, Type))
getTypedHead = \case
  Def f []   -> Just . (f,) . defType <$> getConstInfo f
  Con (ConHead { conName = c }) _ [] -> do
    -- Andreas, 2018-09-08, issue #3211:
    -- discount module parameters for constructor heads
    vs <- freeVarsToApply c
    -- Jesper, 2020-06-17, issue #4755: add dummy arguments in
    -- case we don't have enough parameters
    getNumberOfParameters c >>= \case
      Just npars -> do
        let ws = replicate (npars - size vs) $ defaultArg __DUMMY_TERM__
        t0 <- defType <$> getConstInfo c
        t <- t0 `piApplyM` (vs ++ ws)
        return $ Just (c , t)
      Nothing -> return Nothing
  _ -> return Nothing
