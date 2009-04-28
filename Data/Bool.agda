------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Data.Bool where

open import Data.Function
open import Data.Unit using (⊤)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_ if₁_then_else_

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

not : Bool → Bool
not true  = false
not false = true

-- A function mapping true to an inhabited type and false to an empty
-- type.

T : Bool → Set
T true  = ⊤
T false = ⊥

if_then_else_ : {a : Set} → Bool → a → a → a
if true  then t else f = t
if false then t else f = f

if₁_then_else_ : {A : Set₁} → Bool → A → A → A
if₁ true  then x else y = x
if₁ false then x else y = y

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

------------------------------------------------------------------------
-- Queries

_≟_ : Decidable {Bool} _≡_
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ()
false ≟ true  = no λ()

------------------------------------------------------------------------
-- Some properties

preorder : Preorder
preorder = PropEq.preorder Bool

setoid : Setoid
setoid = PropEq.setoid Bool

decSetoid : DecSetoid
decSetoid = PropEq.decSetoid _≟_
