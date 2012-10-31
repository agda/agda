{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Eliminators where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Utils.Impossible
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Level

#include "../undefined.h"

data ElimView
  = VarElim Nat [Elim]
  | DefElim QName [Elim]
  | ConElim QName [Elim]
  | MetaElim MetaId [Elim]
  | NoElim Term
  deriving (Show)

elimView :: Term -> TCM ElimView
elimView v = do
  -- We can't assume that v has been reduced here in recursive calls,
  -- since reducing a stuck application doesn't necessarily reduces all
  -- the arguments.
  v <- reduce v
  -- domi 2012-7-24: Add unLevel to handle neutral levels. The problem is that reduce turns
  -- suc (neutral) into Level (Max [Plus 1 (NeutralLevel neutral)]) which the below pattern
  -- match does not handle.
  v <- unLevel v
  reportSLn "tc.conv.elim" 50 $ "v = " ++ show v
  case ignoreSharing v of
    Def f vs -> do
      proj <- isProjection f
      case proj of
        Nothing -> DefElim f `app` vs
        Just{}  -> do
          case vs of
            rv : vs' -> elim (Proj f : map Apply vs') <$> elimView (unArg rv)
            [] -> __IMPOSSIBLE__
              -- elimView should only be called from the conversion checker
              -- with properly saturated applications
    Var x vs   -> VarElim x `app` vs
    Con c vs   -> ConElim c `app` vs
    MetaV m vs -> MetaElim m `app` vs
    Lam{}      -> noElim
    Lit{}      -> noElim
    Level{}    -> noElim
    Sort{}     -> noElim
    Pi{}       -> noElim
    DontCare{} -> noElim
    Shared p   -> __IMPOSSIBLE__
    where
      noElim = return $ NoElim v
      app f vs = return $ f $ map Apply vs
      elim :: [Elim] -> ElimView -> ElimView
      elim _    NoElim{}        = __IMPOSSIBLE__
      elim es2 (VarElim  x es1) = VarElim  x (es1 ++ es2)
      elim es2 (DefElim  x es1) = DefElim  x (es1 ++ es2)
      elim es2 (ConElim  x es1) = ConElim  x (es1 ++ es2)
      elim es2 (MetaElim x es1) = MetaElim x (es1 ++ es2)

{- UNUSED
-- | Only used when producing error messages.
unElimView :: ElimView -> Term
unElimView v = case v of
  VarElim x es  -> unElim (Var x []) es
  DefElim x es  -> unElim (Def x []) es
  ConElim x es  -> unElim (Con x []) es
  MetaElim x es -> unElim (MetaV x []) es
  NoElim v      -> v

unElim :: Term -> [Elim] -> Term
unElim v [] = v
unElim v (Apply u : es) = unElim (v `apply` [u]) es
unElim v (Proj f : es)  = unElim (Def f [Arg NotHidden Relevant v]) es
-}
