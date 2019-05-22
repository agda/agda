module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

record R : Set₁ where
  field
    _≡_  : {A : Set} → A → A → Set
    refl : {A : Set} (x : A) → x ≡ x

record R′ (_ : Set) : Set where

module _ (r : R) (_ : {A : Set} → R′ A) where

  open R r

  macro

    m : Term → TC ⊤
    m goal =
      bindTC (unify (def (quote refl)
                         (arg (arg-info visible relevant) unknown ∷ []))
                    goal) λ _ →
      bindTC solveConstraints λ _ →
      bindTC (reduce goal) λ where
        (meta m _) → typeError (strErr "Meta" ∷ [])
        _          → returnTC _

  test : true ≡ true
  test = m

  macro

    m′ : Term → TC ⊤
    m′ goal =
      bindTC (unify (def (quote refl)
                         (arg (arg-info visible relevant) unknown ∷ []))
                    goal) λ _ →
      bindTC (reduce goal) λ where
        goal@(meta m _) →
          bindTC (solveConstraintsMentioning (m ∷ [])) λ _ →
          bindTC (reduce goal) λ where
            (meta _ _) → typeError (strErr "Meta" ∷ [])
            _          → returnTC _
        _ → returnTC _

  test′ : true ≡ true
  test′ = m′
