------------------------------------------------------------------------
-- The Agda standard library
--
-- The type for booleans and some operations
------------------------------------------------------------------------
module Data.Bool.Base where

open import Data.Unit.Base using (⊤)
open import Data.Empty

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

{-# COMPILED_DATA Bool Bool True False #-}

{-# COMPILED_JS Bool  function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILED_JS true  true  #-}
{-# COMPILED_JS false false #-}

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
