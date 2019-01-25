{-# OPTIONS --allow-unsolved-metas #-}

module _ where

open import Agda.Primitive using (Level)

variable
 l : Level

postulate
  Σ : {l' : Level}{X : Set} (Y : X → Set l') -> Set
  _,_ : {l' : Level}{X : Set} {Y : X → Set l'} -> (x : X)(y : Y x) -> Σ Y
  is-universal-element : {l' : Level}{X : Set} {A : X → Set l'} -> Σ A → Set

  universality-section : {X : Set} {A : X → Set l}  -> (x : X) (a : A x)
                          → is-universal-element {X = X} (x , a)
