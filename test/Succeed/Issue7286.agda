{-# OPTIONS -v tc.instance:80 -v tc.decl.instance:80 #-}
open import Agda.Builtin.Nat

record Countable (A : Set) : Set₁ where
  field
    count : A → Nat

open Countable ⦃ ... ⦄

mkCountable : (A : Set) → (A → Nat) → Countable A
mkCountable A c .count = c

data T (A : Set) ⦃ i : Countable A ⦄ : Set where
  mkT : A → T A ⦃ i ⦄

instance
  iN = mkCountable Nat λ n → n

works = mkCountable (T Nat) λ where (mkT n) → n

instance
  fails = mkCountable (T Nat) λ where (mkT n) → n

  -- There are instances whose type is still unsolved
  -- when checking that Nat is a valid argument to a function of type
  -- (A : Set) ⦃ _ : Countable A ⦄ → Set
