{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.Simplify (simplifyTTerm) where

import Control.Arrow (first, second, (***))
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Traversable (traverse)
import Data.List

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.Utils.Maybe

import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Pretty
import Agda.Compiler.Treeless.Compare
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "undefined.h"

data SEnv = SEnv
  { envSubst   :: Substitution' TTerm
  , envRewrite :: [(TTerm, TTerm)] }

type S = Reader SEnv

runS :: S a -> a
runS m = runReader m $ SEnv IdS []

lookupVar :: Int -> S TTerm
lookupVar i = asks $ (`lookupS` i) . envSubst

onSubst :: (Substitution' TTerm -> Substitution' TTerm) -> S a -> S a
onSubst f = local $ \ env -> env { envSubst = f (envSubst env) }

onRewrite :: Substitution' TTerm -> S a -> S a
onRewrite rho = local $ \ env -> env { envRewrite = map (applySubst rho *** applySubst rho) (envRewrite env) }

addRewrite :: TTerm -> TTerm -> S a -> S a
addRewrite lhs rhs = local $ \ env -> env { envRewrite = (lhs, rhs) : envRewrite env }

underLams :: Int -> S a -> S a
underLams i = onRewrite (raiseS i) . onSubst (liftS i)

underLam :: S a -> S a
underLam = underLams 1

underLet :: TTerm -> S a -> S a
underLet u = onRewrite (raiseS 1) . onSubst (\rho -> wkS 1 $ u :# rho)

bindVar :: Int -> TTerm -> S a -> S a
bindVar x u = onSubst (inplaceS x u `composeS`)

rewrite :: TTerm -> S TTerm
rewrite t = do
  rules <- asks envRewrite
  case [ rhs | (lhs, rhs) <- rules, equalTerms t lhs ] of
    rhs : _ -> pure rhs
    []      -> pure t

data FunctionKit = FunctionKit
  { modAux, divAux, natMinus, true, false :: Maybe QName }

simplifyTTerm :: TTerm -> TCM TTerm
simplifyTTerm t = do
  kit <- FunctionKit <$> getBuiltinName builtinNatModSucAux
                     <*> getBuiltinName builtinNatDivSucAux
                     <*> getBuiltinName builtinNatMinus
                     <*> getBuiltinName builtinTrue
                     <*> getBuiltinName builtinFalse
  return $ runS $ simplify kit t

simplify :: FunctionKit -> TTerm -> S TTerm
simplify FunctionKit{..} = simpl
  where
    simpl = rewrite' >=> unchainCase >=> \ t -> case t of

      TDef{}         -> pure t
      TPrim{}        -> pure t

      TVar x  -> do
        v <- lookupVar x
        pure $ if isAtomic v then v else t

      TApp (TDef f) [TLit (LitNat _ 0), m, n, m']
        -- div/mod are equivalent to quot/rem on natural numbers.
        | m == m', Just f == divAux -> simpl $ tOp PQuot n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PRem n (tPlusK 1 m)

      TApp (TPrim _) _ -> pure t  -- taken care of by rewrite'

      TApp f es -> do
        f  <- simpl f
        es <- traverse simpl es
        maybeMinusToPrim f es
      TLam b         -> TLam <$> underLam (simpl b)
      TLit{}         -> pure t
      TCon{}         -> pure t
      TLet e b       -> do
        e <- simpl e
        tLet e <$> underLet e (simpl b)

      TCase x t d bs -> do
        v <- lookupVar x
        let (lets, u) = tLetView v
        case u of                          -- TODO: also for literals
          _ | Just (c, as)     <- conView u   -> simpl $ matchCon lets c as d bs
            | Just (k, TVar y) <- plusKView u -> simpl . mkLets lets . TCase y t d =<< mapM (matchPlusK y x k) bs
          TCase y t1 d1 bs1 -> simpl $ mkLets lets $ TCase y t1 (distrDef case1 d1) $
                                       map (distrCase case1) bs1
            where
              -- Γ x Δ -> Γ _ Δ Θ y, where x maps to y and Θ are the lets
              n     = length lets
              rho   = liftS (x + n + 1) (raiseS 1)    `composeS`
                      singletonS (x + n + 1) (TVar 0) `composeS`
                      raiseS (n + 1)
              case1 = applySubst rho (TCase x t d bs)

              distrDef v d | isUnreachable d = tUnreachable
                           | otherwise       = tLet d v

              distrCase v (TACon c a b) = TACon c a $ TLet b $ raiseFrom 1 a v
              distrCase v (TALit l b)   = TALit l   $ TLet b v
              distrCase v (TAGuard g b) = TAGuard g $ TLet b v

          _ -> do
            d  <- simpl d
            bs <- traverse (simplAlt x) bs
            tCase x t d bs

      TUnit          -> pure t
      TSort          -> pure t
      TErased        -> pure t
      TError{}       -> pure t

    conView (TCon c)           = Just (c, [])
    conView (TApp (TCon c) as) = Just (c, as)
    conView e                  = Nothing

    -- Collapse chained cases (case x of bs -> vs; _ -> case x of bs' -> vs'  ==>
    --                         case x of bs -> vs; bs' -> vs')
    unchainCase :: TTerm -> S TTerm
    unchainCase e@(TCase x t d bs) = do
      let (lets, u) = tLetView d
          k = length lets
      return $ case u of
        TCase y _ d' bs' | x + k == y ->
          mkLets lets $ TCase y t d' $ raise k bs ++ bs'
        _ -> e
    unchainCase e = return e


    mkLets es b = foldr TLet b es

    matchCon _ _ _ d [] = d
    matchCon lets c as d (TALit{}   : bs) = matchCon lets c as d bs
    matchCon lets c as d (TAGuard{} : bs) = matchCon lets c as d bs
    matchCon lets c as d (TACon c' a b : bs)
      | c == c'        = flip (foldr TLet) lets $ mkLet 0 as (raiseFrom a (length lets) b)
      | otherwise      = matchCon lets c as d bs
      where
        mkLet _ []       b = b
        mkLet i (a : as) b = TLet (raise i a) $ mkLet (i + 1) as b

    -- Simplify let y = x + k in case y of j     -> u; _ | g[y]     -> v
    -- to       let y = x + k in case x of j - k -> u; _ | g[x + k] -> v
    matchPlusK :: Int -> Int -> Integer -> TAlt -> S TAlt
    matchPlusK x y k (TALit (LitNat r j) b) = return $ TALit (LitNat r (j - k)) b
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
          v <- lookupVar x
          if v == TVar x then pure v else inline v
        inline (TApp f@TPrim{} args)      = TApp f <$> mapM inline args
        inline u@(TLet _ (TCase 0 _ _ _)) = pure u
        inline (TLet e b)                 = inline (subst 0 e b)
        inline u                          = pure u
    simplPrim t = pure t

    simplPrim' :: TTerm -> TTerm
    simplPrim' (TApp (TPrim PLt) [u, v])
      | Just (PAdd, k, u) <- constArithView u,
        Just (PAdd, j, v) <- constArithView v,
        k == j = tOp PLt u v
    simplPrim' (TApp (TPrim op) [u, v])
      | elem op [PGeq, PLt, PEqI]
      , Just (PAdd, k, u) <- constArithView u
      , Just j <- intView v = TApp (TPrim op) [u, tInt (j - k)]
    simplPrim' (TApp (TPrim PEqI) [u, v])
      | Just (op1, k, u) <- constArithView u,
        Just (op2, j, v) <- constArithView v,
        op1 == op2, k == j,
        elem op1 [PAdd, PSub] = tOp PEqI u v
    simplPrim' (TApp (TPrim PMul) [u, v])
      | Just 0 <- intView u = tInt 0
      | Just 0 <- intView v = tInt 0
    simplPrim' (TApp (TPrim op) [u, v])
      | Just u <- negView u,
        Just v <- negView v,
        elem op [PMul, PQuot] = tOp op u v
      | Just u <- negView u,
        elem op [PMul, PQuot] = simplArith $ tOp PSub (tInt 0) (tOp op u v)
      | Just v <- negView v,
        elem op [PMul, PQuot] = simplArith $ tOp PSub (tInt 0) (tOp op u v)
    simplPrim' (TApp (TPrim PRem) [u, v])
      | Just u <- negView u  = simplArith $ tOp PSub (tInt 0) (tOp PRem u (unNeg v))
      | Just v <- negView v  = tOp PRem u v
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
        operations TVar{}                  = 0
        operations TLit{}                  = 0
        operations _                       = 1000

    rewrite' t = rewrite =<< simplPrim t

    constArithView :: TTerm -> Maybe (TPrim, Integer, TTerm)
    constArithView (TApp (TPrim op) [TLit (LitNat _ k), u])
      | elem op [PAdd, PSub] = Just (op, k, u)
    constArithView (TApp (TPrim op) [u, TLit (LitNat _ k)])
      | op == PAdd = Just (op, k, u)
      | op == PSub = Just (PAdd, -k, u)
    constArithView _ = Nothing

    simplAlt x (TACon c a b) = TACon c a <$> underLams a (maybeAddRewrite (x + a) conTerm $ simpl b)
      where conTerm = mkTApp (TCon c) [TVar i | i <- reverse $ take a [0..]]
    simplAlt x (TALit l b)   = TALit l   <$> maybeAddRewrite x (TLit l) (simpl b)
    simplAlt x (TAGuard g b) = TAGuard   <$> simpl g <*> simpl b

    -- If x is already bound we add a rewrite, otherwise we bind x to rhs.
    maybeAddRewrite x rhs cont = do
      v <- lookupVar x
      case v of
        TVar y | x == y -> bindVar x rhs $ cont
        _ -> addRewrite v rhs cont

    isTrue (TCon c) = Just c == true
    isTrue _        = False

    isFalse (TCon c) = Just c == false
    isFalse _        = False

    maybeMinusToPrim f@(TDef minus) es@[a, b]
      | Just minus == natMinus = do
      b_a  <- rewrite' (tOp PLt b a)
      b_sa <- rewrite' (tOp PLt b (tOp PAdd (tInt 1) a))
      a_b  <- rewrite' (tOp PLt a b)
      if isTrue b_a || isTrue b_sa || isFalse a_b
        then pure $ tOp PSub a b
        else tApp f es

    maybeMinusToPrim f es = tApp f es

    tLet (TVar x) b = subst 0 (TVar x) b
    tLet e (TVar 0) = e
    tLet e b        = TLet e b

    tCase :: Int -> CaseType -> TTerm -> [TAlt] -> S TTerm
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
            tCase x t d (bs' ++ filter noOverlap bs'')
          _ -> tCase' x t d bs'
      where
        bs' = filter (not . isUnreachable) bs

        lookupIfVar (TVar i) = lookupVar i
        lookupIfVar t = pure t

        noOverlap b = not $ any (overlapped b) bs'
        overlapped (TACon c _ _)  (TACon c' _ _) = c == c'
        overlapped (TALit l _)    (TALit l' _)   = l == l'
        overlapped _              _              = False

    -- | Drop unreachable cases for Nat and Int cases.
    pruneLitCases :: Int -> CaseType -> TTerm -> [TAlt] -> S TTerm
    pruneLitCases x CTNat d bs =
      case complete bs [] Nothing of
        Just bs' -> tCase x CTNat tUnreachable bs'
        Nothing  -> return $ TCase x CTNat d bs
      where
        complete bs small (Just upper)
          | null $ [0..upper - 1] \\ small = Just []
        complete (b@(TALit (LitNat _ n) _) : bs) small upper =
          (b :) <$> complete bs (n : small) upper
        complete (b@(TAGuard (TApp (TPrim PGeq) [TVar y, TLit (LitNat _ j)]) _) : bs) small upper | x == y =
          (b :) <$> complete bs small (Just $ maybe j (min j) upper)
        complete _ _ _ = Nothing
    pruneLitCases x CTInt d bs = return $ TCase x CTInt d bs -- TODO
    pruneLitCases x t d bs = return $ TCase x t d bs

    tCase' x t d [] = return d
    tCase' x t d bs = pruneLitCases x t d bs

    tApp :: TTerm -> [TTerm] -> S TTerm
    tApp (TLet e b) es = TLet e <$> underLet e (tApp b (raise 1 es))
    tApp (TCase x t d bs) es = do
      d  <- tApp d es
      bs <- mapM (`tAppAlt` es) bs
      simpl $ TCase x t d bs    -- will resimplify branches
    tApp (TVar x) es = do
      v <- lookupVar x
      case v of
        _ | v /= TVar x && isAtomic v -> tApp v es
        TLam{} -> tApp v es   -- could blow up the code
        _      -> pure $ mkTApp (TVar x) es
    tApp f [] = pure f
    tApp (TLam b) (TVar i : es) = tApp (subst 0 (TVar i) b) es
    tApp (TLam b) (e : es) = tApp (TLet e b) es
    tApp f es = pure $ TApp f es

    tAppAlt (TACon c a b) es = TACon c a <$> underLams a (tApp b (raise a es))
    tAppAlt (TALit l b) es   = TALit l   <$> tApp b es
    tAppAlt (TAGuard g b) es = TAGuard g <$> tApp b es

    isAtomic v = case v of
      TVar{}    -> True
      TCon{}    -> True
      TPrim{}   -> True
      TDef{}    -> True
      TLit{}    -> True
      TSort{}   -> True
      TErased{} -> True
      TError{}  -> True
      _         -> False

type Arith = (Integer, [Atom])

data Atom = Pos TTerm | Neg TTerm
  deriving (Show, Eq, Ord)

aNeg :: Atom -> Atom
aNeg (Pos a) = Neg a
aNeg (Neg a) = Pos a

aCancel :: [Atom] -> [Atom]
aCancel (a : as)
  | elem (aNeg a) as = aCancel (delete (aNeg a) as)
  | otherwise        = a : aCancel as
aCancel [] = []

sortR :: Ord a => [a] -> [a]
sortR = sortBy (flip compare)

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

