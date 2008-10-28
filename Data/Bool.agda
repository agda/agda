------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Data.Bool where

open import Data.Function
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_

------------------------------------------------------------------------
-- The boolean type

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

------------------------------------------------------------------------
-- Some operations

not : Bool -> Bool
not true  = false
not false = true

-- A function mapping true to an inhabited type and false to an empty
-- type.

T : Bool -> Set
T true  = ⊤
T false = ⊥

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if true  then t else f = t
if false then t else f = f

_∧_ : Bool -> Bool -> Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool -> Bool -> Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool -> Bool -> Bool
true  xor b = not b
false xor b = b

------------------------------------------------------------------------
-- Queries

_Bool-≟_ : Decidable {Bool} _≡_
true  Bool-≟ true  = yes ≡-refl
false Bool-≟ false = yes ≡-refl
true  Bool-≟ false = no \()
false Bool-≟ true  = no \()

------------------------------------------------------------------------
-- Some properties

Bool-preorder : Preorder
Bool-preorder = ≡-preorder Bool

Bool-setoid : Setoid
Bool-setoid = ≡-setoid Bool

Bool-decSetoid : DecSetoid
Bool-decSetoid = ≡-decSetoid _Bool-≟_
