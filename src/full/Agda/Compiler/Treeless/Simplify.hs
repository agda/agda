{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
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
underLet u = onRewrite (raiseS 1) . onSubst (\rho -> wkS 1 $ composeS rho (singletonS 0 u))

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
    simpl t = rewrite' t >>= \ t -> case t of

      TDef{}         -> pure t
      TPrim{}        -> pure t

      TVar x  -> do
        v <- lookupVar x
        pure $ if isAtomic v then v else t

      TApp (TDef f) [TLit (LitNat _ 0), m, n, m']
        | m == m', Just f == divAux -> simpl $ tOp PDiv n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PMod n (tPlusK 1 m)

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
        TLet e <$> underLet e (simpl b)

      TCase x t d bs -> do
        v <- lookupVar x
        let (lets, u) = letView v
        case u of                          -- TODO: also for literals
          _ | Just (c, as) <- conView u -> simpl $ matchCon lets c as d bs
          TCase y t1 d1 bs1 -> simpl $ mkLets lets $ TCase y t1 d1 $
                                       map (distrCase case1) bs1
            where
              -- Γ x Δ -> Γ x Δ Θ y, where x maps to y and Θ are the lets
              n     = length lets
              rho   = liftS (x + n + 1) (raiseS 1)    `composeS`
                      singletonS (x + n + 1) (TVar 0) `composeS`
                      raiseS (n + 1)
              case1 = applySubst rho (TCase x t d bs)

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

    letView (TLet e b) = first (e :) $ letView b
    letView e          = ([], e)

    mkLets es b = foldr TLet b es

    matchCon _ _ _ d [] = d
    matchCon lets c as d (TALit{}   : bs) = matchCon lets c as d bs
    matchCon lets c as d (TAGuard{} : bs) = matchCon lets c as d bs
    matchCon lets c as d (TACon c' a b : bs)
      | length as /= a = __IMPOSSIBLE__
      | c == c'        = flip (foldr TLet) lets $ mkLet 0 as (raiseFrom a (length lets) b)
      | otherwise      = matchCon lets c as d bs
      where
        mkLet _ []       b = b
        mkLet i (a : as) b = TLet (raise i a) $ mkLet (i + 1) as b

    simplPrim (TApp f@TPrim{} args) = do
        args    <- mapM simpl args
        inlined <- mapM inline args
        pure $ fromMaybe (TApp f args) $ simplPrim' (TApp f inlined)
      where
        inline (TVar x) = lookupVar x
        inline u        = pure u
    simplPrim t = pure t

    simplPrim' :: TTerm -> Maybe TTerm
    simplPrim' (TApp (TPrim PLt) [u, v])
      | Just (PAdd, k, u) <- constArithView u,
        Just (PAdd, j, v) <- constArithView v,
        k == j = pure $ tOp PLt u v
    simplPrim' u | u == v    = Nothing
                 | otherwise = Just v
      where
        v = simplArith u

    rewrite' t = rewrite =<< simplPrim t

    arithFusion k PAdd j PAdd v = tPlusK (k + j) v
    arithFusion k PAdd j PSub v = tOp PSub (tInt (k + j)) v
    arithFusion k PSub j PAdd v = tOp PSub (tInt (k - j)) v
    arithFusion k PSub j PSub v = tPlusK (k - j) v
    arithFusion _ _ _ _ _ = __IMPOSSIBLE__

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

    maybeAddRewrite x rhs cont = do
      v <- lookupVar x
      case v of
        TVar y | x == y -> cont
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
      if isTrue b_a || isTrue b_sa || isFalse b_a && isFalse a_b
        then pure $ tOp PSub a b
        else tApp f es

    maybeMinusToPrim f es = tApp f es

    tCase :: Int -> CaseType -> TTerm -> [TAlt] -> S TTerm
    tCase x t d bs
      | isUnreachable d =
        case reverse bs' of
          [] -> pure d
          TALit _ b   : as  -> pure $ tCase' x t b (reverse as)
          TAGuard _ b : as  -> pure $ tCase' x t b (reverse as)
          TACon c a b : _   -> pure $ tCase' x t d bs'
      | otherwise = pure $ TCase x t d bs'
      where
        bs' = filter (not . isUnreachable) bs

        tCase' x t d [] = d
        tCase' x t d bs = TCase x t d bs

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
  deriving (Show, Eq)

aNeg :: Atom -> Atom
aNeg (Pos a) = Neg a
aNeg (Neg a) = Pos a

aCancel :: [Atom] -> [Atom]
aCancel (a : as)
  | elem (aNeg a) as = aCancel (delete (aNeg a) as)
  | otherwise        = a : aCancel as
aCancel [] = []

aAdd :: Arith -> Arith -> Arith
aAdd (a, xs) (b, ys) = (a + b, aCancel $ xs ++ ys)

aSub :: Arith -> Arith -> Arith
aSub (a, xs) (b, ys) = (a - b, aCancel $ xs ++ map aNeg ys)

fromArith :: Arith -> TTerm
fromArith (n, []) = tInt n
fromArith (0, xs)
  | (ys, Pos a : zs) <- break isPos xs = foldl addAtom a (ys ++ zs)
  where isPos Pos{} = True
        isPos Neg{} = False
fromArith (n, xs) = foldl addAtom (tInt n) xs

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

