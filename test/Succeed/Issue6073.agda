{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Sub
open import Agda.Primitive.Cubical
open import Agda.Builtin.Nat

module Issue6073 where

“unit” : _
“unit” = Sub Nat i1 λ ._ → 42

“tt” : “unit”
“tt” = inS 42

data _≡ₛ_ {A : SSet} (a : A) : A → SSet where
  reflₛ : a ≡ₛ a

-- demonstrating definitional eta:
_ : ∀ {x y : “unit”} → x ≡ₛ y
_ = reflₛ

refl : ∀ {l} {A : Set l} {x : A} → PathP (λ i → A) x x
refl {x = x} i = x

-- Amy (2022-10-07): This is the same bug as #593. The solution of X
-- should be F (inS 42), since that's the only value that “unit” can
-- have.

bla7 : (F : “unit” → Set) →
  let X : Set
      X = _
  in (z : “unit”) → PathP (λ i → Set) X (F z)
bla7 F z = refl
