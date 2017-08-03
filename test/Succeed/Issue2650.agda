{-# OPTIONS --cubical #-}
module _ where

module _ where
  import Agda.Primitive
  open Agda.Primitive.CubicalPrimitives public

  postulate
    Path' : ∀ {ℓ} {A :     Set ℓ} → A    → A    → Set ℓ
    PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  {-# BUILTIN PATH         Path'     #-}
  {-# BUILTIN PATHP        PathP     #-}

  infix 4 _≡_
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ {A = A} = PathP (λ _ → A)

  Path = _≡_

  refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
  refl {x = x} = \ _ → x


testPath : ∀ {A : Set} {b a : A} (let H : Path b b; H = _) → ∀ i → H i ≡ b
testPath i = refl
