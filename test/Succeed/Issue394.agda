open import Agda.Builtin.Equality

postulate
  A         : Set
  F G H I J : (A : Set₁) → (A → A → Set) → Set
  K         : ⦃ Set → Set → Set ⦄ → { Set → Set → Set } → Set

syntax F A (λ x y → B)               = y ⟨ A ∼ B ⟩₁ x
syntax G A (λ _ y → B)               = y ⟨ A ∼ B ⟩₂
syntax H A (λ x _ → B)               =   ⟨ B ∼ A ⟩₃ x
syntax I A (λ _ _ → B)               =   ⟨ B ∼ A ⟩₄
syntax J A (λ x y → B)               = x y ∶ A ↝ B
syntax K ⦃ λ A B → C ⦄ { λ D E → F } = A B C - D E F

_ : (P ⟨ (Set → Set) ∼ P (Q A) ⟩₁ Q) ≡ F (Set → Set) (λ F G → G (F A))
_ = refl

_ : (P ⟨ (Set → Set) ∼ P A ⟩₂) ≡ G (Set → Set) (λ _ G → G A)
_ = refl

_ : (⟨ Q A ∼ (Set → Set) ⟩₃ Q) ≡ H (Set → Set) (λ F _ → F A)
_ = refl

_ : (⟨ A ∼ (Set → Set) ⟩₄) ≡ I (Set → Set) (λ _ _ → A)
_ = refl

_ : (P Q ∶ (Set → Set) ↝ P (Q A)) ≡ J (Set → Set) (λ F G → F (G A))
_ = refl

_ : (x x x - x x x) ≡ K ⦃ λ _ x → x ⦄ { λ _ y → y }
_ = refl
