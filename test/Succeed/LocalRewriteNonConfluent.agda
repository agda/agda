{-# OPTIONS --local-rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

-- Confluence checking for local rewrite rules is not yet implemented
module LocalRewriteNonConfluent where

module _ (f g : Nat → Nat) (@rew p : ∀ {n} → f (g n) ≡ 0) (@rew q : g 0 ≡ 0)
         where
