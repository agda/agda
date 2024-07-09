{-# OPTIONS --safe --save-metas #-}
module Issue7354.A where

open import Agda.Primitive        public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Sigma    public

record Underlying {ℓ : Level} (T : Set ℓ) : Setω where
  field
    ℓ-underlying : Level
    ⌞_⌟⁰         : T → Set ℓ-underlying

infixr 6 Σ-syntax-und
Σ-syntax-und
  : ∀{ℓ ℓ' : Level}{A : Set ℓ}{{d : Underlying {ℓ} A ⦄
    (X : A) (F : Underlying.⌞_⌟⁰ {ℓ} d X → Set ℓ')
  → Set (ℓ' ⊔ Underlying.ℓ-underlying {ℓ} d)
Σ-syntax-und {ℓ}{ℓ'}{A}{{d}} X F = Σ (Underlying.⌞_⌟⁰ {ℓ} d X) F

instance
  Underlying-Type : ∀{ℓ : Level} → Underlying {lsuc ℓ} (Set ℓ)
  Underlying-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Type {ℓ} .Underlying.⌞_⌟⁰ x = x

foo : ∀(ℓ : Level)(A : Set ℓ)(B : Set)(f : A → B) → Set ℓ
foo ℓ A B f = A → B

bleh : ∀ {ℓ : Level} → Set ℓ → Set → Set ℓ
bleh {ℓ} A B = Σ-syntax-und {lsuc ℓ}{ℓ}{Set ℓ} (A → B) λ f → foo _ _ B f
