module InstanceEtaVisible where

record Inner (A : Set) : Set where
  field inner : A
open Inner {{...}}

record Outer (A : Set) : Set where
  field {{outer}} : Inner A
open Outer {{...}}

module InstanceFieldUnderExplicit
    (X : Set) (F : X → Set) (G : (x : X) → Outer (F x)) where
  test : ∀ x → F x
  test x = inner
