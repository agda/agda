{-# OPTIONS -cpp #-}

-- | Compute eta short normal forms.
module TypeChecking.EtaContract where

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Generic
import TypeChecking.Substitute
import TypeChecking.Free

#include "../undefined.h"
import Utils.Impossible

-- TODO: move to Syntax.Internal.SomeThing
data BinAppView = App Term (Arg Term)
                | NoApp Term

binAppView :: Term -> BinAppView
binAppView t = case ignoreBlocking t of
  Var i xs   -> app (Var i) xs
  Def c xs   -> app (Def c) xs
  Con c xs   -> app (Con c) xs
  Lit _      -> noApp
  Lam _ _    -> noApp
  Pi _ _     -> noApp
  Fun _ _    -> noApp
  Sort _     -> noApp
  MetaV _ _  -> noApp
  BlockedV _ -> __IMPOSSIBLE__
  where
    noApp = NoApp t
    app f [] = noApp
    app f xs = App (f $ init xs) (last xs)

etaContract :: TermLike a => a -> a
etaContract = traverseTerm eta
  where
    eta t@(Lam h b) = case binAppView (absBody b) of
      App u (Arg _ (Var 0 []))
        | not (freeIn 0 u)  -> subst __IMPOSSIBLE__ u
      _ -> t
    eta t = t

