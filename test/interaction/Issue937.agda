-- 2013-11-xx Andreas
-- Previous clauses did not reduce in later clauses under
-- a module telescope.

{-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v interaction.give:20 -v tc.cc:60 -v reify.clause:60 -v tc.section.check:10 -v tc:90 #-}
-- {-# OPTIONS -v tc.lhs:20 #-}
-- {-# OPTIONS -v tc.cover:20 #-}

module Issue937 where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

infixr 4 _,_

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
proj₂ ex = s≤s z≤n -- works

ex' : Σ Nat (λ n → zero < n)
proj₁ ex' = suc zero
proj₂ ex' = {! s≤s z≤n !}

module _ (A : Set) where

  ex'' : Σ Nat (λ n → zero < n)
  proj₁ ex'' = suc zero
  proj₂ ex'' = s≤s z≤n -- works

  ex''' : Σ Nat (λ n → zero < n)
  proj₁ ex''' = suc zero
  proj₂ ex''' = {! s≤s z≤n !}

-- The normalized goals should be printed as 1 ≤ 1
