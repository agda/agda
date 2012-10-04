{-# LANGUAGE CPP #-}

-- | Compute eta short normal forms.
module Agda.TypeChecking.EtaContract where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad
import {-# SOURCE #-} Agda.TypeChecking.Records
import {-# SOURCE #-} Agda.TypeChecking.Datatypes
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- TODO: move to Agda.Syntax.Internal.SomeThing
data BinAppView = App Term (Arg Term)
                | NoApp Term

binAppView :: Term -> BinAppView
binAppView t = case t of
  Var i xs   -> app (Var i) xs
  Def c xs   -> app (Def c) xs
  Con c xs   -> app (Con c) xs
  Lit _      -> noApp
  Level _    -> noApp   -- could be an application, but let's not eta contract levels
  Lam _ _    -> noApp
  Pi _ _     -> noApp
  Sort _     -> noApp
  MetaV _ _  -> noApp
  DontCare _ -> noApp
  Shared p   -> binAppView (derefPtr p)  -- destroys sharing
  where
    noApp = NoApp t
    app f [] = noApp
    app f xs = App (f $ init xs) (last xs)

etaContract :: TermLike a => a -> TCM a
etaContract = traverseTermM etaOnce

etaOnce :: Term -> TCM Term
etaOnce v = eta v
  where
    eta v@Shared{} = updateSharedTerm eta v
    eta t@(Lam h (Abs _ b)) = do  -- NoAbs can't be eta'd
      imp <- shouldEtaContractImplicit
      case binAppView b of
        App u (Arg h' r v)
          | (r == Irrelevant || isVar0 v) && allowed imp h' && not (freeIn 0 u) ->
            return $ subst __IMPOSSIBLE__ u
        _ -> return t
      where
        isVar0 (Shared p)               = isVar0 (derefPtr p)
        isVar0 (Var 0 [])               = True
        isVar0 (Level (Max [Plus 0 l])) = case l of
          NeutralLevel v   -> isVar0 v
          UnreducedLevel v -> isVar0 v
          BlockedLevel{}   -> False
          MetaLevel{}      -> False
        isVar0 _ = False
        allowed imp h' = h == h' && (imp || h == NotHidden)
    eta t@(Con c args) = do
      r <- getConstructorData c
      ifM (isEtaRecord r)
          (etaContractRecord r c args)
          (return t)
    eta t = return t
