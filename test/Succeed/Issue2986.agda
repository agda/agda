{-# OPTIONS --cubical #-}
module _ where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Nat

postulate
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATHP        PathP     #-}

postulate
  A : Set
  a : A
  b : A
  p : PathP (\ _ → A) a b


test1 : ∀ {p : PathP (\ _ → A) a a} {P : A → Set} → P (p i0) → P a
test1 x = x

test2 : ∀ {P : A → Set} → P (p i0) → P a
test2 x = x

q : (x : Nat) → PathP (\ _ → Nat) x x
q zero i = zero
q (suc n) i = suc (q n i)

test3 : ∀ {P : Nat → Set}{n : Nat} → P (q n i0) → P n
test3 x = x
