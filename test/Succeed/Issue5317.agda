{-# OPTIONS --erasure #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit

-- (*)
-- Andreas, 2025-08-08, issue #7001
-- Erasure status needs to be given explicitly
-- at inferred lambdas now, if --erasure is on.

macro

  m-0 : Term → TC ⊤
  m-0 goal =
    bindTC (inferType goal) λ where
      (pi (arg (arg-info _ (modality _ quantity-0)) _) _) →
        bindTC (quoteTC (λ (@0 _ : Set) → Set))  -- (*)
               (unify goal)
      type → typeError (termErr type ∷ [])

  m-ω : Term → TC ⊤
  m-ω goal =
    bindTC (inferType goal) λ where
      (pi (arg (arg-info _ (modality _ quantity-ω)) _) _) →
        bindTC (quoteTC (λ (@ω _ : Set) → Set))  -- (*)
               (unify goal)
      type → typeError (termErr type ∷ [])

_ : @0 Set → Set₁
_ = m-0

_ : @ω Set → Set₁
_ = m-ω

postulate
  f : @0 Set₁ → Set₁

macro

  m₁ : Set₁ → Term → TC ⊤
  m₁ A goal =
    bindTC (quoteTC A) λ A →
    unify goal
      (def (quote f)
         (arg (arg-info visible (modality relevant quantity-0)) A ∷
          []))

_ : Set₁ → Set₁
_ = λ A → m₁ A

macro

  m₂ : Set₁ → Term → TC ⊤
  m₂ A goal =
    bindTC (quoteTC A) λ A →
    unify goal
      (def (quote f)
                                -- The modality is ignored.
         (arg (arg-info visible (modality irrelevant quantity-ω)) A ∷
          []))

_ : Set₁ → Set₁
_ = λ A → m₂ A
