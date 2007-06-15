------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Prelude.Bool where

open import Prelude.Logic
open import Prelude.Function
open import Prelude.BinaryRelation
open import Prelude.BinaryRelation.PropositionalEquality

infixr 7 _⊕_
infixr 6 _∧_
infixr 5 _∨_

------------------------------------------------------------------------
-- The type

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

------------------------------------------------------------------------
-- Some operations

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if true  then t else f = t
if false then t else f = f

_∧_ : Bool -> Bool -> Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool -> Bool -> Bool
true  ∨ b = true
false ∨ b = b

not : Bool -> Bool
not true  = false
not false = true

-- Exclusive or.

_⊕_ : Bool -> Bool -> Bool
true  ⊕ b = not b
false ⊕ b = b

------------------------------------------------------------------------
-- Queries

abstract

  true≢false : ¬ true ≡ false
  true≢false ()

  _Bool-≟_ : Decidable {Bool} _≡_
  true  Bool-≟ true  = yes ≡-refl
  false Bool-≟ false = yes ≡-refl
  true  Bool-≟ false = no (⊥-elim ∘ true≢false)
  false Bool-≟ true  = no (⊥-elim ∘ true≢false ∘ ≡-sym)

------------------------------------------------------------------------
-- Some properties

Bool-preSetoid : PreSetoid
Bool-preSetoid = ≡-preSetoid Bool

Bool-setoid : Setoid
Bool-setoid = ≡-setoid Bool

Bool-decSetoid : DecSetoid
Bool-decSetoid = record { setoid = Bool-setoid; _≟_ = _Bool-≟_ }
