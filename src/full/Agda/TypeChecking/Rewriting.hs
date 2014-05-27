{-# LANGUAGE CPP #-}

-- | Rewriting with arbitrary rules.
--
--   The user specifies a relation symbol by the pragma
--   @
--       {-# BUILTIN REWRITE rel #-}
--   @
--   where @rel@ should be of type @Δ → (lhs rhs : A) → Set i@.
--
--   Then the user can add rewrite rules by the pragma
--   @
--       {-# REWRITE q #-}
--   @
--   where @q@ should be a closed term of type @Γ → rel us lhs rhs@.
--
--   We then intend to add a rewrite rule
--   @
--       Γ ⊢ lhs ↦ rhs : B
--   @
--   to the signature where @B = A[us/Δ]@.
--
--   To this end, we normalize @lhs@, which should be of the form
--   @
--       f ts
--   @
--   for a @'Def'@-symbol f (postulate, function, data, record, constructor).
--   Further, @FV(ts) = dom(Γ)@.
--   The rule @q :: Γ ⊢ f ts ↦ rhs : B@ is added to the signature
--   to the definition of @f@.
--
--   When reducing a term @Ψ ⊢ f vs@ is stuck, we try the rewrites for @f@,
--   by trying to unify @vs@ with @ts@.
--   This is for now done by substituting fresh metas Xs for the bound
--   variables in @ts@ and checking equality with @vs@
--   @
--       Ψ ⊢ (f ts)[Xs/Γ] = f vs : B[Xs/Γ]
--   @
--   If successful (no open metas/constraints), we replace @f vs@ by
--   @rhs[Xs/Γ]@ and continue reducing.

module Agda.TypeChecking.Rewriting where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Check that the name given to the BUILTIN REWRITE is actually
--   a relation symbol.
--   I.e., its type should be of the form @Δ → (lhs rhs : A) → Set ℓ@.
--   Note: we do not care about hiding/non-hiding of lhs and rhs.
verifyBuiltinRewrite :: Term -> Type -> TCM ()
verifyBuiltinRewrite v t = do
  let failure reason = typeError . GenericDocError =<< sep
       [ prettyTCM v <+> text " does not have the right type for a rewriting relation"
       , reason
       ]
  TelV tel core <- telView t
  case ignoreSharing (unEl core) of
    Sort{} -> do
      -- Check that the types of the last two arguments are equal.
      let n                = size tel
          (delta, lastTwo) = splitAt (n - 2) $ telToList tel
      when (size lastTwo < 2) $
        failure $ text "because it should accept at least two arguments"
      let [a, b] = snd . unDom <$> lastTwo
      unlessM (tryConversion $ inTopContext $ addContext delta $ addContext (head lastTwo) $ equalType (raise 1 a) b) $
        failure $ text $ "because the types of the last two arguments are different"
    Level{}  -> __IMPOSSIBLE__
    Lam{}    -> __IMPOSSIBLE__
    Pi{}     -> __IMPOSSIBLE__
    Shared{} -> __IMPOSSIBLE__
    _ -> failure $ text "because its type does not end in a sort, but in "
           <+> do inTopContext $ addContext tel $ prettyTCM core

addRewriteRule :: QName -> TCM ()
addRewriteRule q = return ()
