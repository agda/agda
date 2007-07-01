------------------------------------------------------------------------
-- Lexicographic induction
------------------------------------------------------------------------

module Logic.Induction.Lexicographic where

open import Logic.Induction
open import Data.Product

LexRecPred : Set -> Set -> Set1
LexRecPred a b = (a -> b -> Set) -> (a -> b -> Set)

LexRec : forall {a b} -> RecPred a -> RecPred b -> LexRecPred a b
LexRec RecA RecB = \P x y ->
  -- Either x is constant and y is smaller, ...
  RecB (P x) y ×
  -- ...or x is smaller and y is arbitrary.
  RecA (\x' -> forall y' -> P x' y') x

lexRecBuilder
  :  forall {a b}
  -> {RecA : RecPred a} (recA : RecursorBuilder RecA)
  -> {RecB : RecPred b} (recB : RecursorBuilder RecB)
  -> (P : a -> b -> Set)
  -> (forall x y -> LexRec RecA RecB P x y -> P x y)
  -> forall x y -> LexRec RecA RecB P x y
lexRecBuilder {RecA = RecA} recA {RecB = RecB} recB P f =
  \x y -> (p₁ x y (p₂ x) , p₂ x)
  where
  p₁ :  forall x y
     -> RecA (\x' -> forall y' -> P x' y') x
     -> RecB (P x) y
  p₁ x y x-rec = recB (P x)
                      (\y y-rec -> f x y (y-rec , x-rec))
                      y

  p₂ : forall x -> RecA (\x' -> forall y' -> P x' y') x
  p₂ = recA (\x -> forall y -> P x y)
            (\x x-rec y ->
                f x y (p₁ x y x-rec , x-rec))

lexRec
  :  forall {a b}
  -> {RecA : RecPred a} (recA : RecursorBuilder RecA)
  -> {RecB : RecPred b} (recB : RecursorBuilder RecB)
  -> (P : a -> b -> Set)
  -> (forall x y -> LexRec RecA RecB P x y -> P x y)
  -> forall x y -> P x y
lexRec recA recB P f x y =
  f x y (lexRecBuilder recA recB P f x y)
