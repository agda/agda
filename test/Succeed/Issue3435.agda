
module _ where

infix  -1 _■
infixr -2 step-∼

postulate
  Transitive : {A : Set} (P Q : A → A → Set) → Set

  step-∼ : ∀ {A} {P Q : A → A → Set}
             ⦃ t : Transitive P Q ⦄ x {y z} →
             Q y z → P x y → Q x z

syntax step-∼ x Qyz Pxy = x ∼⟨ Pxy ⟩ Qyz

infix 4 _≈_
postulate
  Proc  : Set
  _≈_   : Proc → Proc → Set
  _■    : ∀ x → x ≈ x
  instance trans : Transitive  _≈_ _≈_

module DummyInstances where

  postulate
    R₁ R₂ R₃ R₄ R₅ : Proc → Proc → Set

  postulate
    instance
      transitive₁₁ : Transitive R₁ R₁
      transitive₁₂ : Transitive R₁ R₂
      transitive₁₃ : Transitive R₁ R₃
      transitive₁₄ : Transitive R₁ R₄
      transitive₁₅ : Transitive R₁ R₅
      transitive₂₁ : Transitive R₂ R₁
      transitive₂₂ : Transitive R₂ R₂
      transitive₂₃ : Transitive R₂ R₃
      transitive₂₄ : Transitive R₂ R₄
      transitive₂₅ : Transitive R₂ R₅
      transitive₃₁ : Transitive R₃ R₁
      transitive₃₂ : Transitive R₃ R₂
      transitive₃₃ : Transitive R₃ R₃
      transitive₃₄ : Transitive R₃ R₄
      transitive₃₅ : Transitive R₃ R₅
      transitive₄₁ : Transitive R₄ R₁
      transitive₄₂ : Transitive R₄ R₂
      transitive₄₃ : Transitive R₄ R₃
      transitive₄₄ : Transitive R₄ R₄
      transitive₄₅ : Transitive R₄ R₅
      transitive₅₁ : Transitive R₅ R₁
      transitive₅₂ : Transitive R₅ R₂
      transitive₅₃ : Transitive R₅ R₃
      transitive₅₄ : Transitive R₅ R₄
      transitive₅₅ : Transitive R₅ R₅

postulate
  comm : ∀ {P} → P ≈ P
  P    : Proc

cong : P ≈ P
cong =
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ∼⟨ comm ⟩
  P ■
