{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteNoEta where

module _ (x : Nat) (@rew _ : x ≡ 0) where
  foo : Nat
  foo = 0

  bar : Nat
  bar = 0

-- Note that η equality for the @rew function space requires comparing bodies
-- in possibly definitionally inconsistent contexts.
-- Therefore, |@rew A → B| should not satisfy η
eta : foo 1 ≡ bar 1
eta = refl
