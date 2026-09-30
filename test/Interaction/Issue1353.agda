{-# OPTIONS --show-implicit #-}
{-# OPTIONS -v tc.interaction:20 #-}

------------------------------------------------------------------------
-- Library

id : ∀ {X : Set} → X → X
id x = x

infixr 9 _∘_

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

record Σ (X : Set) (Y : X → Set) : Set where
  constructor _,_
  field
    proj₁ : X
    proj₂ : Y proj₁

open Σ public

syntax Σ X (λ x → Y) = Σ[ x ∈ X ] Y

data _≡_ {X : Set} (x : X) : X → Set where
  refl : x ≡ x

subst : ∀ {A} (P : A → Set) {x y} → x ≡ y → P x → P y
subst P refl p = p

record _▷_ (I O : Set) : Set₁ where
  constructor _◃_/_
  field
    Parameter  : (o : O) → Set
    Arity      : ∀ {o} (p : Parameter o) → Set
    input      : ∀ {o} (p : Parameter o) (a : Arity p) → I

open _▷_ public

Pow : Set → Set₁
Pow X = X → Set

infix 4 _⊆_

_⊆_ : ∀ {X} → Pow X → Pow X → Set
P ⊆ Q = ∀ {x} → P x → Q x

⟦_⟧ : ∀ {I O} → I ▷ O → (Pow I → Pow O)
⟦ P ◃ A / s ⟧ X o = Σ[ p ∈ P o ] ((a : A p) → X (s p a))

Alg : ∀ {O} → O ▷ O → Pow O → Set
Alg Σ X = ⟦ Σ ⟧ X ⊆ X

module _ {I₁ I₂ O₁ O₂} where

  record ContainerMorphism
         (C₁ : I₁ ▷ O₁) (C₂ : I₂ ▷ O₂)
         (f : I₁ → I₂) (g : O₁ → O₂)
         (_∼_ : I₂ → I₂ → Set) (_≈_ : Set → Set → Set)
         (_·_ : ∀ {A B} → A ≈ B → A → B) :
         Set where
    field
      parameter  : Parameter C₁ ⊆ Parameter C₂ ∘ g
      arity      : ∀ {o} {p₁ : Parameter C₁ o} →
                   Arity C₂ (parameter p₁) ≈ Arity C₁ p₁
      coherent   : ∀ {o} {p₁ : Parameter C₁ o} {a₂ : Arity C₂ (parameter p₁)} →
                   f (input C₁ p₁ (arity · a₂)) ∼ input C₂ (parameter p₁) a₂

  open ContainerMorphism public

  _⇒[_/_]_ : I₁ ▷ O₁ → (I₁ → I₂) → (O₁ → O₂) →
             I₂ ▷ O₂ → Set
  C₁ ⇒[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_  (λ R₂ R₁ → R₂ → R₁)
                                                      (λ f x → f x)

⟪_⟫ : ∀ {I} {C₁ C₂ : I ▷ I} →
      C₁ ⇒[ id / id ] C₂ → (X : Pow I) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
⟪ m ⟫ X (c , k) = parameter m c , λ a₂ →
  subst X (coherent m) (k (arity m a₂))

------------------------------------------------------------------------
-- Example

weaken : ∀ {I} {Ω : I ▷ I} {Ψ : I ▷ I} {X : Pow I} →
         Alg Ψ X → Ω ⇒[ id / id ] Ψ → Alg Ω X
weaken {I}{Ω}{Ψ}{X = X} φ m {i} (p , k) = φ {x = i} (⟪ m ⟫ {!X!} (p , k))

weaken2 : ∀ {I} {Ω : I ▷ I} {Ψ : I ▷ I} {X : Pow I} →
          Alg Ψ X → Ω ⇒[ id / id ] Ψ → Alg Ω X
weaken2 {I}{Ω}{Ψ}{X = X} φ m {i} (p , k) = φ {i} (⟪ m ⟫ X (p , k))
