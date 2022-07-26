{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Box : Set → Set₁ where
  box : (A : Set) → Box A

data D (A : Set) : Set₁ where
  c : A → Box A → D A

postulate
  any : {A : Set} → A
  one : {A : Set} → D A
  rew : ∀ A → c any (box A) ≡ one
{-# REWRITE rew #-}

test : c tt (box ⊤) ≡ one
test = refl
