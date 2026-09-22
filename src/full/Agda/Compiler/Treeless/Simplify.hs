{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Treeless.Simplify (simplifyTTerm) where

import Control.Applicative
import Control.Monad        ( (>=>), guard )
import Control.Monad.Reader ( MonadReader(..), asks, Reader, runReader )
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.List as List

import Agda.Syntax.Internal (termSize)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Compare

import Agda.Utils.IndexMap (IndexMap)
import qualified Agda.Utils.IndexMap as IndexMap
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Tuple ( (***), second )

import Agda.Utils.Impossible

data SEnv = SEnv
  { envSubst :: Substitution' TTerm
  , envStrictness :: IndexMap Strictness
    -- ^ What strictness was the given variable bound with?
  , envRewrite :: [(TTerm, TTerm)] }

type S = Reader SEnv

runS :: S a -> a
runS m = runReader m $ SEnv IdS IndexMap.nil []

lookupVar :: Int -> S (Strictness, TTerm)
lookupVar i = do
  env <- ask
  return (IndexMap.index i (envStrictness env), lookupS (envSubst env) i)

onSubst :: (Substitution' TTerm -> Substitution' TTerm) -> S a -> S a
onSubst f = local $ \ env -> env { envSubst = f (envSubst env) }

onStrictness :: (IndexMap Strictness -> IndexMap Strictness) -> S a -> S a
onStrictness f =
  local (\env -> env { envStrictness = f (envStrictness env) })

onRewrite :: Substitution' TTerm -> S a -> S a
onRewrite rho = local $ \ env -> env { envRewrite = map (applySubst rho *** applySubst rho) (envRewrite env) }

addRewrite :: TTerm -> TTerm -> S a -> S a
addRewrite lhs rhs = local $ \ env -> env { envRewrite = (lhs, rhs) : envRewrite env }

-- | There is one strictness per binding, and the first element in the
-- list corresponds to the first new binding.

underLams :: [Strictness] -> S a -> S a
underLams ss =
  onRewrite (raiseS i) . onSubst (liftS i) .
  onStrictness (flip IndexMap.append ss)
  where
  i = length ss

underLam :: Strictness -> S a -> S a
underLam s = underLams [s]

underLet :: Strictness -> TTerm -> S a -> S a
underLet s u =
  onRewrite (raiseS 1) . onSubst (\rho -> wkS 1 $ u :# rho) .
  onStrictness (flip IndexMap.snoc s)

bindVar :: Int -> Strictness -> TTerm -> S a -> S a
bindVar x s u =
  onSubst (inplaceS x u `composeS`) .
  onStrictness (IndexMap.update x s)

rewrite :: TTerm -> S TTerm
rewrite t = do
  rules <- asks envRewrite
  case [ rhs | (lhs, rhs) <- rules, equalTerms t lhs ] of
    rhs : _ -> pure rhs
    []      -> pure t

data FunctionKit = FunctionKit
  { modAux, divAux, natMinus, true, false :: Maybe QName }

simplifyTTerm :: EvaluationStrategy -> TTerm -> TCM TTerm
simplifyTTerm eval t = do
  kit <- FunctionKit <$> getBuiltinName builtinNatModSucAux
                     <*> getBuiltinName builtinNatDivSucAux
                     <*> getBuiltinName builtinNatMinus
                     <*> getBuiltinName builtinTrue
                     <*> getBuiltinName builtinFalse
  return $ runS $ simplify eval kit t

simplify :: EvaluationStrategy -> FunctionKit -> TTerm -> S TTerm
simplify eval FunctionKit{ divAux, modAux, natMinus, true, false } =
  simpl
  where
    simpl = rewrite' >=> unchainCase >=> \case

      t@TDef{}  -> pure t
      t@TPrim{} -> pure t
      t@TVar{}  -> pure t

      TApp (TDef f) [TLit (LitNat 0), m, n, m']
        -- div/mod are equivalent to quot/rem on natural numbers.
        | m == m', Just f == divAux -> simpl $ tOp PQuot n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PRem n (tPlusK 1 m)

      -- Word64 primitives --

      --  toWord (a ∙ b) == toWord a ∙64 toWord b
      TPFn PITo64 (TPOp op a b)
        | Just op64 <- opTo64 op -> simpl $ tOp op64 (TPFn PITo64 a) (TPFn PITo64 b)
        where
          opTo64 op = lookup op [(PAdd, PAdd64), (PSub, PSub64), (PMul, PMul64),
                                 (PQuot, PQuot64), (PRem, PRem64)]

      t@(TApp (TPrim _) _) -> pure t  -- taken care of by rewrite'

      TCoerce t -> TCoerce <$> simpl t

      TApp f es -> do
        f  <- simpl f
        es <- traverse simpl es
        maybeMinusToPrim f es
      TLam b     -> TLam <$> underLam (defaultStrictness eval) (simpl b)
      t@TLit{}   -> pure t
      t@TCon{}   -> pure t
      TLet s e b -> do
        simpl e >>= \case
          TPFn P64ToI a -> do
            -- Inline calls to P64ToI since these trigger optimisations.
            -- Ideally, the optimisations would trigger anyway, but at the
            -- moment they only do if inlining the entire let looks like a
            -- good idea.
            let rho = inplaceS 0 (TPFn P64ToI (TVar 0))
            tLet s a <$> underLet s a (simpl (applySubst rho b))
          e -> tLet s e <$> underLet s e (simpl b)

      TCase x t d bs -> do
        (_, v) <- lookupVar x
        let (lets, u) = tLetView v
        (d, bs) <-
          pruneBoolGuards d <$>
            traverse (simplAlt x (caseInduction t)) bs
        case u of                          -- TODO: also for literals
          _ | Just (c, as) <- conView u ->
              simpl $ matchCon lets c as (caseInduction t) d bs
            | Just (k, TVar y) <- plusKView u -> simpl . mkLets lets . TCase y t d =<< mapM (matchPlusK y x k) bs
            -- We are not normalizing the case-of-case commuting converison
            -- since it can lead to major code duplication without join points
            -- or continuations. See issue #7595.
            | otherwise -> do
            d <- simpl d
            tCase x t d bs

      t@TUnit    -> pure t
      t@TSort    -> pure t
      t@TErased  -> pure t
      t@TError{} -> pure t

    conView (TCon c)    = Just (c, [])
    conView (TApp f as) = second (++ as) <$> conView f
    conView e           = Nothing

    -- Collapse chained cases (case x of bs -> vs; _ -> case x of bs' -> vs'  ==>
    --                         case x of bs -> vs; bs' -> vs')
    unchainCase :: TTerm -> S TTerm
    unchainCase e@(TCase x t d bs) = do
      let (lets, u) = tLetView d
          k = length lets
      case u of
        TCase y _ d' bs' | x + k == y -> do
          lets <- runMaybeT (mapM safeLet lets)
          return $ case lets of
            Just lets ->
              mkLets lets $ TCase y t d' $
              raise k bs ++ filter (`noOverlap` bs) bs'
            Nothing -> e
        _ -> return e
    unchainCase e = return e

    -- If chained cases of the following form are collapsed, and the
    -- lets moved to the outside, then performance could take a hit
    -- (see issue #8767):
    --
    --   case x of
    --     ⋮
    --     _ -> let … in case y of …
    --
    -- If strict evaluation is used, then this transformation is only
    -- allowed if all let bindings are "safe", i.e. non-strict or
    -- (heuristically) cheap to compute. If non-strict evaluation is
    -- used, then "unsafe" bindings are made non-strict.

    safeLet :: (Strictness, TTerm) -> MaybeT S (Strictness, TTerm)
    safeLet l@(NonStrict, _) =
      return l
    safeLet l@(Strict, t) = MaybeT $ do
      t' <- runMaybeT (do
        -- The number 30 does not have any special significance other
        -- than being "not too small, but not very large".
        guard (termSize t < 30)
        cheap t)
      return $ case t' of
        Just t  -> Just (Strict, t)
        Nothing -> case eval of
          LazyEvaluation _ -> Just (NonStrict, t)
          EagerEvaluation  -> Nothing
      where
      cheap :: TTerm -> MaybeT S TTerm
      cheap t = case t of
        -- Error calls should definitely not be evaluated prematurely.
        TError{} -> empty
        -- Case expressions and top-level definitions are treated as
        -- expensive.
        TCase{} -> empty
        TDef{}  -> empty
        -- Strictly bound variables are treated as cheap.
        TVar x -> do
          (s, _) <- lift (lookupVar x)
          case s of
            NonStrict -> empty
            Strict    -> return t
        -- Lets, coercions and applications of primitives are handled
        -- recursively.
        TLet s t1 t2 -> uncurry TLet <$> safeLet (s, t1) <*> cheap t2
        TCoerce t    -> TCoerce <$> cheap t
        TApp t args  -> case t of
          TPrim p -> TApp <$> (if cheapPrim p then return (TPrim p)
                               else empty)
                          <*> mapM cheap args
          _       -> empty
        -- Things that are known to be (basically) values are treated
        -- as cheap.
        TPrim{}   -> return t
        TLam{}    -> return t
        TLit{}    -> return t
        TCon{}    -> return t
        TUnit{}   -> return t
        TSort{}   -> return t
        TErased{} -> return t

      cheapPrim = \case
        -- String comparison might be expensive.
        PEqS -> False
        -- If expressions are treated as expensive, just like case
        -- expressions.
        PIf -> False
        -- All other primitives are treated as cheap, including PSeq.
        PSeq    -> True
        PAdd    -> True
        PAdd64  -> True
        PSub    -> True
        PSub64  -> True
        PMul    -> True
        PMul64  -> True
        PQuot   -> True
        PQuot64 -> True
        PRem    -> True
        PRem64  -> True
        PGeq    -> True
        PLt     -> True
        PLt64   -> True
        PEqI    -> True
        PEq64   -> True
        PEqF    -> True
        PEqC    -> True
        PEqQ    -> True
        PITo64  -> True
        P64ToI  -> True

    mkLets es b = foldr (uncurry TLet) b es

    matchCon _ _ _ _ d [] = d
    matchCon lets c as i d (TALit{}   : bs) = matchCon lets c as i d bs
    matchCon lets c as i d (TAGuard{} : bs) = matchCon lets c as i d bs
    matchCon lets c as i d (TACon c' a b : bs)
      | c == c'   = flip (foldr (uncurry TLet)) lets $
                    mkLet 0 as (raiseFrom a (length lets) b)
      | otherwise = matchCon lets c as i d bs
      where
      s = defaultConstructorStrictness eval i

      mkLet _ []       b = b
      mkLet i (a : as) b = TLet s (raise i a) $ mkLet (i + 1) as b

    -- Simplify let y = x + k in case y of j     -> u; _ | g[y]     -> v
    -- to       let y = x + k in case x of j - k -> u; _ | g[x + k] -> v
    matchPlusK :: Int -> Int -> Integer -> TAlt -> S TAlt
    matchPlusK x y k (TALit (LitNat j) b) = return $ TALit (LitNat (j - k)) b
    matchPlusK x y k (TAGuard g b) = flip TAGuard b <$> simpl (applySubst (inplaceS y (tPlusK k (TVar x))) g)
    matchPlusK x y k TACon{} = __IMPOSSIBLE__
    matchPlusK x y k TALit{} = __IMPOSSIBLE__

    simplPrim (TApp f@TPrim{} args) = do
        args    <- mapM simpl args
        inlined <- mapM inline args
        let u = TApp f args
            v = simplPrim' (TApp f inlined)
        pure $ if v `betterThan` u then v else u
      where
        inline (TVar x)                   = do
          (_, v) <- lookupVar x
          if v == TVar x then pure v else inline v
        inline (TApp f@TPrim{} args)        = TApp f <$> mapM inline args
        inline u@(TLet _ _ (TCase 0 _ _ _)) = pure u
        inline (TLet _ e b)                 = inline (subst 0 e b)
        inline u                            = pure u
    simplPrim t = pure t

    simplPrim' :: TTerm -> TTerm
    simplPrim' (TApp (TPrim PSeq) (u : v : vs))
      | u == v             = mkTApp v vs
      | TApp TCon{} _ <- u = mkTApp v vs
      | TApp TLit{} _ <- u = mkTApp v vs
    simplPrim' (TApp (TPrim PLt) [u, v])
      | Just (PAdd, k, u) <- constArithView u,
        Just (PAdd, j, v) <- constArithView v,
        k == j = tOp PLt u v
      | Just (PSub, k, u) <- constArithView u,
        Just (PSub, j, v) <- constArithView v,
        k == j = tOp PLt v u
      | Just (PAdd, k, v) <- constArithView v,
        TApp (TPrim P64ToI) [u] <- u,
        k >= 2 ^ 64, Just trueCon <- true = TCon trueCon
      | Just k <- intView u
      , Just j <- intView v
      , Just trueCon <- true
      , Just falseCon <- false = if k < j then TCon trueCon else TCon falseCon
    simplPrim' (TApp (TPrim PGeq) [u, v])
      | Just (PAdd, k, u) <- constArithView u,
        Just (PAdd, j, v) <- constArithView v,
        k == j = tOp PGeq u v
      | Just (PSub, k, u) <- constArithView u,
        Just (PSub, j, v) <- constArithView v,
        k == j = tOp PGeq v u
      | Just k <- intView u
      , Just j <- intView v
      , Just trueCon <- true
      , Just falseCon <- false = if k >= j then TCon trueCon else TCon falseCon
    simplPrim' (TApp (TPrim op) [u, v])
      | op `elem` [PGeq, PLt, PEqI]
      , Just (PAdd, k, u) <- constArithView u
      , Just j <- intView v = TApp (TPrim op) [u, tInt (j - k)]
    simplPrim' (TApp (TPrim PEqI) [u, v])
      | Just (op1, k, u) <- constArithView u,
        Just (op2, j, v) <- constArithView v,
        op1 == op2, k == j,
        op1 `elem` [PAdd, PSub] = tOp PEqI u v
    simplPrim' (TPOp op u v)
      | zeroL, isMul || isDiv = tInt 0
      | zeroL, isAdd          = v
      | zeroR, isMul          = tInt 0
      | zeroR, isAdd || isSub = u
      where zeroL = Just 0 == intView u || Just 0 == word64View u
            zeroR = Just 0 == intView v || Just 0 == word64View v
            isAdd = op `elem` [PAdd, PAdd64]
            isSub = op `elem` [PSub, PSub64]
            isMul = op `elem` [PMul, PMul64]
            isDiv = op `elem` [PQuot, PQuot64, PRem, PRem64]
    simplPrim' (TApp (TPrim op) [u, v])
      | Just u <- negView u,
        Just v <- negView v,
        op `elem` [PMul, PQuot] = tOp op u v
      | Just u <- negView u,
        op `elem` [PMul, PQuot] = simplArith $ tOp PSub (tInt 0) (tOp op u v)
      | Just v <- negView v,
        op `elem` [PMul, PQuot] = simplArith $ tOp PSub (tInt 0) (tOp op u v)
    simplPrim' (TApp (TPrim PRem) [u, v])
      | Just u <- negView u  = simplArith $ tOp PSub (tInt 0) (tOp PRem u (unNeg v))
      | Just v <- negView v  = tOp PRem u v

      -- (fromWord a == fromWord b) = (a ==64 b)
    simplPrim' (TPOp op (TPFn P64ToI a) (TPFn P64ToI b))
        | Just op64 <- opTo64 op = tOp op64 a b
        where
          opTo64 op = lookup op [(PEqI, PEq64), (PLt, PLt64)]

      -- toWord/fromWord k == fromIntegral k
    simplPrim' (TPFn PITo64 (TLit (LitNat n)))    = TLit (LitWord64 (fromIntegral n))
    simplPrim' (TPFn P64ToI (TLit (LitWord64 n))) = TLit (LitNat    (fromIntegral n))

      -- toWord (fromWord a) == a
    simplPrim' (TPFn PITo64 (TPFn P64ToI a)) = a

    simplPrim' (TApp f@(TPrim op) [u, v]) = simplArith $ TApp f [simplPrim' u, simplPrim' v]
    simplPrim' u = u

    unNeg u | Just v <- negView u = v
            | otherwise           = u

    negView (TApp (TPrim PSub) [a, b])
      | Just 0 <- intView a = Just b
    negView _ = Nothing

    -- Count arithmetic operations
    betterThan u v = operations u <= operations v
      where
        operations (TApp (TPrim _) [a, b]) = 1 + operations a + operations b
        operations (TApp (TPrim PSeq) (a : _))
          | notVar a                       = 1000000  -- only seq on variables!
        operations (TApp (TPrim _) [a])    = 1 + operations a
        operations TVar{}                  = 0
        operations TLit{}                  = 0
        operations TCon{}                  = 0
        operations TDef{}                  = 0
        operations _                       = 1000

        notVar TVar{} = False
        notVar _      = True

    rewrite' t = rewrite =<< simplPrim t

    constArithView :: TTerm -> Maybe (TPrim, Integer, TTerm)
    constArithView (TApp (TPrim op) [TLit (LitNat k), u])
      | op `elem` [PAdd, PSub] = Just (op, k, u)
    constArithView (TApp (TPrim op) [u, TLit (LitNat k)])
      | op == PAdd = Just (op, k, u)
      | op == PSub = Just (PAdd, -k, u)
    constArithView _ = Nothing

    simplAlt x i (TACon c a b) =
      TACon c a <$>
        underLams (replicate a (defaultConstructorStrictness eval i))
          (maybeAddRewrite (x + a) conTerm $ simpl b)
      where
      conTerm = mkTApp (TCon c) $ map TVar $ downFrom a
    simplAlt x _ (TALit l b) =
      TALit l <$> maybeAddRewrite x (TLit l) (simpl b)
    simplAlt x _ (TAGuard g b) =
      TAGuard <$> simpl g <*> simpl b

    -- If x is already bound we add a rewrite, otherwise we bind x to rhs.
    maybeAddRewrite x rhs cont = do
      (s, v) <- lookupVar x
      case v of
        TVar y | x == y -> bindVar x s rhs $ cont
        _ -> addRewrite v rhs cont

    isTrue (TCon c) = Just c == true
    isTrue _        = False

    isFalse (TCon c) = Just c == false
    isFalse _        = False

    maybeMinusToPrim f@(TDef minus) es@[a, b]
      | Just minus == natMinus = do
      leq  <- checkLeq b a
      if leq then pure $ tOp PSub a b
             else tApp f es

    maybeMinusToPrim f es = tApp f es

    tLet _ (TVar x) b = subst 0 (TVar x) b
    tLet _ e (TVar 0) = e
    tLet s e b        = TLet s e b

    tCase :: Int -> CaseInfo -> TTerm -> [TAlt] -> S TTerm
    tCase x t d [] = pure d
    tCase x t d bs
      | isUnreachable d =
        case reverse bs' of
          [] -> pure d
          TALit _ b   : as  -> tCase x t b (reverse as)
          TAGuard _ b : as  -> tCase x t b (reverse as)
          TACon c a b : _   -> tCase' x t d bs'
      | otherwise = do
        d' <- lookupIfVar d
        case d' of
          TCase y _ d bs'' | x == y ->
            tCase x t d (bs' ++ filter (`noOverlap` bs') bs'')
          _ -> tCase' x t d bs'
      where
        bs' = filter (not . isUnreachable) bs

        lookupIfVar (TVar i) = snd <$> lookupVar i
        lookupIfVar t = pure t

    noOverlap b bs = not $ any (overlapped b) bs

    overlapped (TACon c _ _)  (TACon c' _ _) = c == c'
    overlapped (TALit l _)    (TALit l' _)   = l == l'
    overlapped _              _              = False

    -- Drop unreachable cases for Nat and Int cases.
    pruneLitCases :: Int -> CaseInfo -> TTerm -> [TAlt] -> S TTerm
    pruneLitCases x t d bs | CTNat == caseType t =
      case complete bs [] Nothing of
        Just bs' -> tCase x t tUnreachable bs'
        Nothing  -> return $ TCase x t d bs
      where
        complete bs small (Just upper)
          | null $ [0..upper - 1] List.\\ small = Just []
        complete (b@(TALit (LitNat n) _) : bs) small upper =
          (b :) <$> complete bs (n : small) upper
        complete (b@(TAGuard (TApp (TPrim PGeq) [TVar y, TLit (LitNat j)]) _) : bs) small upper | x == y =
          (b :) <$> complete bs small (Just $ maybe j (min j) upper)
        complete _ _ _ = Nothing

    pruneLitCases x t d bs
      | CTInt == caseType t = return $ TCase x t d bs -- TODO
      | otherwise           = return $ TCase x t d bs

    -- Drop 'false' branches and drop everything after 'true' branches (including the default
    -- branch)
    pruneBoolGuards d [] = (d, [])
    pruneBoolGuards d (b@(TAGuard (TCon c) _) : bs)
      | Just c == true  = (tUnreachable, [b])
      | Just c == false = pruneBoolGuards d bs
    pruneBoolGuards d (b : bs) =
      second (b :) $ pruneBoolGuards d bs

    tCase' x t d [] = return d
    tCase' x t d bs = pruneLitCases x t d bs

    tApp :: TTerm -> [TTerm] -> S TTerm
    tApp (TLet s e b) es = TLet s e <$> underLet s e (tApp b (raise 1 es))
    tApp (TCase x t d bs) es = do
      d  <- tApp d es
      bs <- mapM (flip (tAppAlt (caseInduction t)) es) bs
      simpl $ TCase x t d bs    -- will resimplify branches
    tApp (TVar x) es = do
      (_, v) <- lookupVar x
      case v of
        _ | v /= TVar x && isAtomic v -> tApp v es
        TLam{} -> tApp v es   -- could blow up the code
        _      -> pure $ mkTApp (TVar x) es
    tApp f [] = pure f
    tApp (TLam b) (TVar i : es) = tApp (subst 0 (TVar i) b) es
    tApp (TLam b) (e : es) =
      tApp (TLet (defaultStrictness eval) e b) es
      -- Applications are strict in strict backends and non-strict in
      -- non-strict backends.
    tApp f es = pure $ TApp f es

    tAppAlt i (TACon c a b) es =
      TACon c a <$>
        underLams (replicate a (defaultConstructorStrictness eval i))
          (tApp b (raise a es))
    tAppAlt _ (TALit l b) es   = TALit l   <$> tApp b es
    tAppAlt _ (TAGuard g b) es = TAGuard g <$> tApp b es

    isAtomic = \case
      TVar{}    -> True
      TCon{}    -> True
      TPrim{}   -> True
      TDef{}    -> True
      TLit{}    -> True
      TSort{}   -> True
      TErased{} -> True
      TError{}  -> True
      _         -> False

    checkLeq a b = do
      rho  <- asks envSubst
      rwr  <- asks envRewrite
      let nf = toArith . applySubst rho
          less = [ (nf a, nf b) | (TPOp PLt a b, rhs) <- rwr, isTrue  rhs ]
          leq  = [ (nf b, nf a) | (TPOp PLt a b, rhs) <- rwr, isFalse rhs ]

          match (j, as) (k, bs)
            | as == bs  = Just (j - k)
            | otherwise = Nothing

          -- Do we have x ≤ y given x' < y' + d ?
          matchEqn d x y (x', y') = isJust $ do
            k <- match x x'     -- x = x' + k
            j <- match y y'     -- y = y' + j
            guard (k <= j + d)  -- x ≤ y if k ≤ j + d

          matchLess = matchEqn 1
          matchLeq  = matchEqn 0

          literal (j, []) (k, []) = j <= k
          literal _ _ = False

          -- k + fromWord x ≤ y  if  k + 2^64 - 1 ≤ y
          wordUpperBound (k, [Pos (TApp (TPrim P64ToI) _)]) y = go (k + 2 ^ 64 - 1, []) y
          wordUpperBound _ _ = False

          -- x ≤ k + fromWord y  if  x ≤ k
          wordLowerBound a (k, [Pos (TApp (TPrim P64ToI) _)]) = go a (k, [])
          wordLowerBound _ _ = False

          go x y = or
            [ literal x y
            , wordUpperBound x y
            , wordLowerBound x y
            , any (matchLess x y) less
            , any (matchLeq x y) leq ]

      return $ go (nf a) (nf b)

type Arith = (Integer, [Atom])

data Atom = Pos TTerm | Neg TTerm
  deriving (Show, Eq, Ord)

aNeg :: Atom -> Atom
aNeg (Pos a) = Neg a
aNeg (Neg a) = Pos a

aCancel :: [Atom] -> [Atom]
aCancel (a : as)
  | (aNeg a) `elem` as = aCancel (List.delete (aNeg a) as)
  | otherwise          = a : aCancel as
aCancel [] = []

sortR :: Ord a => [a] -> [a]
sortR = List.sortBy (flip compare)

aAdd :: Arith -> Arith -> Arith
aAdd (a, xs) (b, ys) = (a + b, aCancel $ sortR $ xs ++ ys)

aSub :: Arith -> Arith -> Arith
aSub (a, xs) (b, ys) = (a - b, aCancel $ sortR $ xs ++ map aNeg ys)

fromArith :: Arith -> TTerm
fromArith (n, []) = tInt n
fromArith (0, xs)
  | (ys, Pos a : zs) <- break isPos xs = foldl addAtom a (ys ++ zs)
fromArith (n, xs)
  | n < 0, (ys, Pos a : zs) <- break isPos xs =
    tOp PSub (foldl addAtom a (ys ++ zs)) (tInt (-n))
fromArith (n, xs) = foldl addAtom (tInt n) xs

isPos :: Atom -> Bool
isPos Pos{} = True
isPos Neg{} = False

addAtom :: TTerm -> Atom -> TTerm
addAtom t (Pos a) = tOp PAdd t a
addAtom t (Neg a) = tOp PSub t a

toArith :: TTerm -> Arith
toArith t | Just n <- intView t = (n, [])
toArith (TApp (TPrim PAdd) [a, b]) = aAdd (toArith a) (toArith b)
toArith (TApp (TPrim PSub) [a, b]) = aSub (toArith a) (toArith b)
toArith t = (0, [Pos t])

simplArith :: TTerm -> TTerm
simplArith = fromArith . toArith
