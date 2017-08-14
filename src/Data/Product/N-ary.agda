------------------------------------------------------------------------
-- The Agda standard library
--
-- N-ary products
------------------------------------------------------------------------

-- Vectors (as in Data.Vec) also represent n-ary products, so what is
-- the point of this module? The n-ary products below are intended to
-- be used with a fixed n, in which case the nil constructor can be
-- avoided: pairs are represented as pairs (x , y), not as triples
-- (x , y , unit).

module Data.Product.N-ary where

open import Data.Nat hiding (_^_)
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function.Inverse
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- N-ary product.

infix 8 _^_

_^_ : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
A ^ 0           = Lift ⊤
A ^ 1           = A
A ^ suc (suc n) = A × A ^ suc n

-- Conversions.

↔Vec : ∀ {a} {A : Set a} n → A ^ n ↔ Vec A n
↔Vec n = record
  { to         = P.→-to-⟶ (toVec n)
  ; from       = P.→-to-⟶ fromVec
  ; inverse-of = record
    { left-inverse-of  = fromVec∘toVec n
    ; right-inverse-of = toVec∘fromVec
    }
  }
  where
  toVec : ∀ {a} {A : Set a} n → A ^ n → Vec A n
  toVec 0             (lift tt) = []
  toVec 1             x         = [ x ]
  toVec (suc (suc n)) (x , xs)  = x ∷ toVec _ xs

  fromVec : ∀ {a} {A : Set a} {n} → Vec A n → A ^ n
  fromVec []           = lift tt
  fromVec (x ∷ [])     = x
  fromVec (x ∷ y ∷ xs) = (x , fromVec (y ∷ xs))

  fromVec∘toVec : ∀ {a} {A : Set a} n (xs : A ^ n) →
                  fromVec (toVec n xs) ≡ xs
  fromVec∘toVec 0                   (lift tt)    = P.refl
  fromVec∘toVec 1                   x            = P.refl
  fromVec∘toVec 2                   (x , y)      = P.refl
  fromVec∘toVec (suc (suc (suc n))) (x , y , xs) =
    P.cong (_,_ x) (fromVec∘toVec (suc (suc n)) (y , xs))

  toVec∘fromVec : ∀ {a} {A : Set a} {n} (xs : Vec A n) →
                  toVec n (fromVec xs) ≡ xs
  toVec∘fromVec []           = P.refl
  toVec∘fromVec (x ∷ [])     = P.refl
  toVec∘fromVec (x ∷ y ∷ xs) = P.cong (_∷_ x) (toVec∘fromVec (y ∷ xs))
