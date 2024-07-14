-- See #7271
{-# OPTIONS --type-based-termination #-}

module TypeBasedTermination.InfiniteLowerBound where

data ⊥ : Set where

record _×_ (A B : Set) : Set where
  field
    fstt : A
    snd : B
open _×_

record U : Set where
  coinductive; constructor delay
  field force : U × ⊥
open U

f : U → U × ⊥
f u = u' .force
   where u' = u

u : U
u .force = f u

absurd : ⊥
absurd = u .force .snd
