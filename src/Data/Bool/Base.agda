------------------------------------------------------------------------
-- The Agda standard library
--
-- The type for booleans and some operations
------------------------------------------------------------------------
module Data.Bool.Base where

open import Data.Unit.Base using (⊤)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Core

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_

------------------------------------------------------------------------
-- The boolean type

open import Agda.Builtin.Bool public

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

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

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

infix 4 _≟_

_≟_ : Decidable {A = Bool} _≡_
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ()
false ≟ true  = no λ()
