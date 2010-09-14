module MixfixBinders where

postulate
  M      : Set → Set
  return : ∀ {A} → A → M A
  bind   : ∀ {A B} → M A → (A → M B) → M B

infixr 40 bind
syntax bind m (λ x → m′) = x ← m , m′

postulate
  X : Set
  m₁ m₂ m₃ : M X
  f : X → X → X

foo : M X
foo = x₁ ← m₁ ,
      x₂ ← m₂ ,
      x₃ ← m₃ ,
      return (f x₁ (f x₂ x₃))

infixr 10 Σ _,_
syntax Σ A (λ x → B) = Σ x ∈ A , B
data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ x ∈ A , B x

infix 50 _≤_
postulate
  _≤_ : X → X → Set
  x₁ x₂ : X
  le : x₁ ≤ x₂

p : Σ x ∈ X , Σ y ∈ X , x ≤ y
p = x₁ , x₂ , le