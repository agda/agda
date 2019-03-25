-- In Agda 2.5.3 the error was:

-- μ₂ is not strictly positive, because it occurs
-- in the third argument to ⟦_⟧
-- in the type of the constructor fix
-- in the definition of μ₂.

open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

Σ# : {n : ℕ} -> (Fin n -> Set) -> Set
Σ# {zero} f = ⊥
Σ# {suc zero} f = f zero
Σ# {suc n} f = f zero ⊎ Σ# {n} λ i -> f (suc i)

module Matrices {Ix : Set} {Σ : (Ix -> Set) -> Set} where

  Matrix : Set1
  Matrix = (i j : Ix) -> Set

  _<+>_ : Matrix -> Matrix -> Matrix
  m <+> n = λ i j -> m i j ⊎ n i j

  _<*>_ : Matrix -> Matrix -> Matrix
  m <*> n = λ i j -> Σ λ k -> m i k × n k j

data Poly {Coeffs : Set1} : Set1 where
  0p 1p : Poly
  X : Poly
  _+_ _*_ : (D1 D2 : Poly {Coeffs}) -> Poly {Coeffs}
  K : Coeffs -> Poly

module Dim {n : ℕ} where
  open Matrices {Fin n} {Σ#}

  ⟦_⟧ : Poly {Vec (Vec Set n) n} -> Matrix -> Matrix
  ⟦ 0p ⟧ x i j = ⊥
  ⟦ 1p ⟧ x i j = ⊤
  ⟦ X ⟧ x i j = x i j
  ⟦ D1 + D2 ⟧ x i j = (⟦ D1 ⟧ x <+> ⟦ D2 ⟧ x) i j
  ⟦ D1 * D2 ⟧ x i j = (⟦ D1 ⟧ x <*> ⟦ D2 ⟧ x) i j
  ⟦ K S ⟧ x i j = lookup (lookup S i) j

  ⟪_⟫ : Poly {Set} -> Set → Set
  ⟪ 0p ⟫ x = ⊥
  ⟪ 1p ⟫ x = ⊤
  ⟪ X ⟫ x = x
  ⟪ D1 + D2 ⟫ x = (⟪ D1 ⟫ x ⊎ ⟪ D2 ⟫ x)
  ⟪ D1 * D2 ⟫ x = (⟪ D1 ⟫ x × ⟪ D2 ⟫ x)
  ⟪ K S ⟫ x = S

  data μ₁ (p : Poly) : Set where
    fix : ⟪ p ⟫ (μ₁ p) -> μ₁ p

  data μ₂ (p : Poly) (i j : Fin n) : Set where
    fix : ⟦ p ⟧ (μ₂ p) i j -> μ₂ p i j
