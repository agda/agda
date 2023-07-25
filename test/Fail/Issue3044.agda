{-# OPTIONS --large-indices #-}
-- The error on Agda 2.5.3 was:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Substitute/Class.hs:209

open import Agda.Primitive using (_⊔_ ; Level ; lsuc)

record Unit {U : Level} : Set U where
-- error still occurs with no constructors or fields in these types
  constructor unit

record _×_ {U V : Level} (A : Set U) (B : Set V) : Set (U ⊔ V) where
  constructor _,,_
  field
    x : A
    y : B

infixr 25 _×_

data _⇔_ {U V : Level} : (A : Set U) → (B : Set V) → Set (U ⊔ V) where
  unitIL : {A : Set U} → A ⇔ A × Unit
