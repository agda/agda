{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Subst where

import Control.Applicative
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import Data.Maybe

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.TypeChecking.Substitute

instance DeBruijn TTerm where
  debruijnVar = TVar
  debruijnView (TVar i) = Just i
  debruijnView _ = Nothing

instance Subst TTerm TTerm where
  applySubst IdS t = t
  applySubst rho t = case t of
    TDef{}    -> t
    TLit{}    -> t
    TCon{}    -> t
    TPrim{}   -> t
    TUnit{}   -> t
    TSort{}   -> t
    TErased{} -> t
    TError{}  -> t
    TVar i         -> lookupS rho i
    TApp f ts      -> TApp (applySubst rho f) (applySubst rho ts)
    TLam b         -> TLam (applySubst (liftS 1 rho) b)
    TLet e b       -> TLet (applySubst rho e) (applySubst (liftS 1 rho) b)
    TCase i t d bs ->
      case applySubst rho (TVar i) of
        TVar j  -> TCase j t (applySubst rho d) (applySubst rho bs)
        e       -> TLet e $ TCase 0 t (applySubst rho' d) (applySubst rho' bs)
          where rho' = wkS 1 rho

instance Subst TTerm TAlt where
  applySubst rho (TACon c i b) = TACon c i (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)   = TALit l (applySubst rho b)
  applySubst rho (TAGuard g b) = TAGuard (applySubst rho g) (applySubst rho b)

data UnderLambda = YesUnderLambda | NoUnderLambda
  deriving (Eq, Ord, Show)

data Occurs = Occurs Int UnderLambda
  deriving (Eq, Ord, Show)

once :: Occurs
once = Occurs 1 NoUnderLambda

underLambda :: Occurs -> Occurs
underLambda o = o <> Occurs 0 YesUnderLambda

instance Monoid UnderLambda where
  mempty = NoUnderLambda
  mappend YesUnderLambda _            = YesUnderLambda
  mappend _ YesUnderLambda            = YesUnderLambda
  mappend NoUnderLambda NoUnderLambda = NoUnderLambda

instance Monoid Occurs where
  mempty = Occurs 0 NoUnderLambda
  mappend (Occurs a k) (Occurs b l) = Occurs (a + b) (k <> l)

class HasFree a where
  freeVars :: a -> Map Int Occurs

freeIn :: HasFree a => Int -> a -> Bool
freeIn i x = Map.member i (freeVars x)

occursIn :: HasFree a => Int -> a -> Occurs
occursIn i x = fromMaybe mempty $ Map.lookup i (freeVars x)

instance HasFree Int where
  freeVars x = Map.singleton x once

instance HasFree a => HasFree [a] where
  freeVars xs = Map.unionsWith mappend $ map freeVars xs

instance (HasFree a, HasFree b) => HasFree (a, b) where
  freeVars (x, y) = Map.unionWith mappend (freeVars x) (freeVars y)

data Binder a = Binder Int a

instance HasFree a => HasFree (Binder a) where
  freeVars (Binder 0 x) = freeVars x
  freeVars (Binder k x) = Map.filterWithKey (\ k _ -> k >= 0) $ Map.mapKeysMonotonic (subtract k) $ freeVars x

instance HasFree TTerm where
  freeVars t = case t of
    TDef{}    -> Map.empty
    TLit{}    -> Map.empty
    TCon{}    -> Map.empty
    TPrim{}   -> Map.empty
    TUnit{}   -> Map.empty
    TSort{}   -> Map.empty
    TErased{} -> Map.empty
    TError{}  -> Map.empty
    TVar i         -> freeVars i
    TApp f ts      -> freeVars (f, ts)
    TLam b         -> underLambda <$> freeVars (Binder 1 b)
    TLet e b       -> freeVars (e, Binder 1 b)
    TCase i _ d bs -> freeVars (i, (d, bs))

instance HasFree TAlt where
  freeVars a = case a of
    TACon _ i b -> freeVars (Binder i b)
    TALit _ b   -> freeVars b
    TAGuard g b -> freeVars (g, b)

