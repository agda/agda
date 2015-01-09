------------------------------------------------------------------------
-- The Agda standard library
--
-- Some unit types
------------------------------------------------------------------------

module Data.Unit.NonEta where

open import Level

------------------------------------------------------------------------
-- A unit type defined as a data-type

-- The ⊤ type (see Data.Unit) comes with η-equality, which is often
-- nice to have, but sometimes it is convenient to be able to stop
-- unfolding (see "Hidden types" below).

data Unit : Set where
  unit : Unit

------------------------------------------------------------------------
-- Hidden types

-- "Hidden" values.

Hidden : ∀ {a} → Set a → Set a
Hidden A = Unit → A

-- The hide function can be used to hide function applications. Note
-- that the type-checker doesn't see that "hide f x" contains the
-- application "f x".

hide : ∀ {a b} {A : Set a} {B : A → Set b} →
       ((x : A) → B x) → ((x : A) → Hidden (B x))
hide f x unit = f x

-- Reveals a hidden value.

reveal : ∀ {a} {A : Set a} → Hidden A → A
reveal f = f unit
