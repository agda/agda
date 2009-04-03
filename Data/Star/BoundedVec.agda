------------------------------------------------------------------------
-- Bounded vectors (inefficient implementation)
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.Star.BoundedVec where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Decoration
open import Data.Star.Pointer
open import Data.Star.List using (List)
open import Data.Unit
open import Data.Function
import Data.Maybe as Maybe
open import Relation.Binary
open import Relation.Binary.Consequences
open import Category.Monad

------------------------------------------------------------------------
-- The type

-- Finite sets decorated with elements (note the use of suc).

BoundedVec : Set → ℕ → Set
BoundedVec a n = Any (λ _ → a) (λ _ → ⊤) (suc n)

[] : ∀ {a n} → BoundedVec a n
[] = this tt

infixr 5 _∷_

_∷_ : ∀ {a n} → a → BoundedVec a n → BoundedVec a (suc n)
_∷_ = that

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : ∀ {a n} → BoundedVec a n → BoundedVec a (suc n)
↑ {a} = gmap inc lift
  where
  open RawMonad Maybe.monad

  inc = _<$>_ (map-NonEmpty suc)

  lift : Pointer (λ _ → a) (λ _ → ⊤) =[ inc ]⇒
         Pointer (λ _ → a) (λ _ → ⊤)
  lift (step x) = step x
  lift (done _) = done _

------------------------------------------------------------------------
-- Conversions

fromList : ∀ {a} → (xs : List a) → BoundedVec a (length xs)
fromList ε        = []
fromList (x ◅ xs) = x ∷ fromList xs

toList : ∀ {a n} → BoundedVec a n → List a
toList xs = gmap (const tt) decoration (init xs)
