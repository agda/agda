{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record R : Set where
  constructor mkR
  field
    f : Nat

data Box : Set → Set₁ where
  box : (A : Set) → Box A

data D (A : Set) : Set₁ where
  c : Box A → R → D A

postulate
  r   : R
  dr  : ∀ {A} → D A
  rew : ∀ {A} {x} → c {A} (box A) (mkR x) ≡ dr
{-# REWRITE rew #-}

test : c {Bool} (box Bool) r ≡ dr
test = refl
