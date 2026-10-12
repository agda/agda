-- Andreas, 2025-10-12, issue #8830
-- Test case by Mietek Bak
-- Fails to resolve instance with Agda up to 2.8.0.
-- Already fixed on master

module Issue8830 where

open import Agda.Builtin.Sigma

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A : Set} → A → M A
    _>>=_  : ∀ {A B : Set} → M A → (A → M B) → M B

open Monad {{...}}

module Fails where
  pair : ∀ {M : Set → Set} {{monad : Monad M}}
           {A : Set} {B : A → Set} →
           (a : A) → M (B a) → M (Σ A B)
  pair a mb = mb >>= λ b → return (a , b)

{-
_r_20 : Monad (λ v → _M_32 v)  [ at Bug.agda:16.28-34 ]
_M_32 : Set → Set  [ at Bug.agda:16.28-34 ]
_B_33 : A → Set  [ at Bug.agda:16.38-39 ]

———— Error —————————————————————————————————————————————————
error: [UnsolvedConstraints]
Failed to solve the following constraints:
  Resolve instance argument _r_20 : Monad (λ v → _M_32 v)
  No candidates yet
    (blocked on _B_33)
      [ at Bug.agda:16.28-34 ]
  _M_32 (Σ A (λ v → _B_33 v)) =< M (Σ A B) (blocked on _M_32)
  B a = _B_33 a : Set (blocked on _B_33)
-}

module Works1 where
  data Dummy : Set where
    _,_ : Dummy → Dummy → Dummy

  pair : ∀ {M : Set → Set} {{monad : Monad M}}
           {A : Set} {B : A → Set} →
           (a : A) → M (B a) → M (Σ A B)
  pair a mb = mb >>= λ b → return (a , b)

module Works2 where
  pair : ∀ {M : Set → Set} {{monad : Monad M}}
           {A : Set} {B : A → Set} →
           (a : A) → M (B a) → M (Σ A B)
  pair {B = B} a mb = mb >>= λ (b : B a) → return (a , b)

module Works3 where
  pair : ∀ {M : Set → Set} {{monad : Monad M}}
           {A : Set} {B : A → Set} →
           (a : A) → M (B a) → M (Σ A B)
  pair {M} a mb = mb >>= λ b → return {M} (a , b)
