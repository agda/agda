------------------------------------------------------------------------
-- The Agda standard library
--
-- Signs
------------------------------------------------------------------------

module Data.Sign where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core using (_≡_; refl)
-- Importing Core here ^^^ to keep a small import list

-- Signs.

data Sign : Set where
  - : Sign
  + : Sign

-- Decidable equality.

infix 4 _≟_

_≟_ : Decidable {A = Sign} _≡_
- ≟ - = yes refl
- ≟ + = no λ()
+ ≟ - = no λ()
+ ≟ + = yes refl

-- The opposite sign.

opposite : Sign → Sign
opposite - = +
opposite + = -

-- "Multiplication".

infixl 7 _*_

_*_ : Sign → Sign → Sign
+ * s₂ = s₂
- * s₂ = opposite s₂
