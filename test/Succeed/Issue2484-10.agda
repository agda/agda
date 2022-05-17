{-# OPTIONS --sized-types #-}

module _ (_ : Set) where

open import Agda.Builtin.Size

postulate
  I : Set

record ∃ (B : I → Set) : Set where
  constructor _,_
  field
    proj₁ : I
    proj₂ : B proj₁

module M (_ : Set₁) where

  mutual

    data P (i : Size) (x y : I) : Set where
      ⟨_⟩ : ∃ (Q i x) → P i x y

    record Q (i : Size) (x y : I) : Set where
      coinductive
      field
        force : {j : Size< i} → P j x y

open M Set

postulate
  map   : (B : I → Set) → (∀ x → B x → B x) → ∃ B → ∃ B
  lemma : ∀ x y i → Q i x y → Q i x y

p  : ∀ x i → P i x x
q′ : ∀ x i → ∃ λ y → Q i x y
q  : ∀ x i → Q i x x

q′ x i              = x , q x i
p x i               = ⟨ map _ (λ y → lemma x y i) (q′ x _) ⟩
Q.force (q x i) {j} = p _ _
