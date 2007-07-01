------------------------------------------------------------------------
-- Lexicographic induction
------------------------------------------------------------------------

module Logic.Induction.Lexicographic where

open import Logic.Induction
open import Data.Product

-- The structure of lexicographic induction.

_⊗_ : forall {a b} -> RecStruct a -> RecStruct b -> RecStruct (a × b)
_⊗_ RecA RecB P (x , y) =
  -- Either x is constant and y is "smaller", ...
  RecB (\y' -> P (x , y')) y
    ×
  -- ...or x is "smaller" and y is arbitrary.
  RecA (\x' -> forall y' -> P (x' , y')) x

-- Constructs a recursor builder for lexicographic induction.

[_⊗_]
  :  forall {a} {RecA : RecStruct a} -> RecursorBuilder RecA
  -> forall {b} {RecB : RecStruct b} -> RecursorBuilder RecB
  -> RecursorBuilder (RecA ⊗ RecB)
[_⊗_] {RecA = RecA} recA {RecB = RecB} recB P f (x , y) =
  (p₁ x y p₂x , p₂x)
  where
  p₁ :  forall x y
     -> RecA (\x' -> forall y' -> P (x' , y')) x
     -> RecB (\y' -> P (x , y')) y
  p₁ x y x-rec = recB (\y' -> P (x , y'))
                      (\y y-rec -> f (x , y) (y-rec , x-rec))
                      y

  p₂ : forall x -> RecA (\x' -> forall y' -> P (x' , y')) x
  p₂ = recA (\x -> forall y -> P (x , y))
            (\x x-rec y -> f (x , y) (p₁ x y x-rec , x-rec))

  p₂x = p₂ x
