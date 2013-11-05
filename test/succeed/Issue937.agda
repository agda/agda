{-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v interaction.give:20 -v tc.cc:60 -v reify.clause:60 -v tc.section.check:10 -v tc:90 #-}
-- {-# OPTIONS -v tc.lhs:20 #-}

module Issue937 where

open import Common.Equality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

data _≤_ : Nat → Nat → Set  where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

ex : Σ Nat (λ n → zero < n)
proj₁ ex = suc zero
proj₂ ex = s≤s z≤n

module _ (A : Set) where

  ex'' : Σ Nat (λ n → zero < n)
  proj₁ ex'' = suc zero
  proj₂ ex'' = s≤s z≤n

test : ex'' Nat ≡ (suc zero , s≤s z≤n)
test = refl
