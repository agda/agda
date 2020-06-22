{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  T  : (Set → Set → Set) → Set
  T₀ : Set

module _ (F : Set → Set) where

  postulate rew : T (λ X Y → F X) ↦ T₀

  {-# REWRITE rew #-}

  test : T (λ X Y → F X) ≡ T₀
  test = refl
