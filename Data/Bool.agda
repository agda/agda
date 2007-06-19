------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Data.Bool where

open import Logic
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixr 6 _∧_
infixr 5 _∨_ _xor_

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

_xor_ : Bool -> Bool -> Bool
true  xor b = not b
false xor b = b

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
