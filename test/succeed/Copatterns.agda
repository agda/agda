{-# OPTIONS --copatterns #-}
module Copatterns where

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_

pair : {A B : Set} → A → B → A × B
fst (pair a b) = a
snd (pair a b) = b

swap : {A B : Set} → A × B → B × A
fst (swap p) = snd p
snd (swap p) = fst p

swap3 : {A B C : Set} → A × (B × C) → C × (B × A)
fst (swap3 t)       = snd (snd t)
fst (snd (swap3 t)) = fst (snd t)
snd (snd (swap3 t)) = fst t

swap4 : {A B C D : Set} → A × (B × (C × D)) → D × (C × (B × A))
fst (swap4 t)             = snd (snd (snd t))
fst (snd (swap4 t))       = fst (snd (snd t))
fst (snd (snd (swap4 t))) = fst (snd t)
snd (snd (snd (swap4 t))) = fst t
