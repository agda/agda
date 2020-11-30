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

-- Jesper, 2020-06-17: Ideally Agda should reject the above rewrite
-- rule, since it causes reduction to be unstable under eta-conversion
works : c any (box ⊤) ≡ c tt (box ⊤)
works = refl

-- However, currently it is accepted, breaking subject reduction:
{-# REWRITE rew #-}

fails : c any (box ⊤) ≡ c tt (box ⊤)
fails = refl
