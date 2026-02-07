module InstanceEtaVisible2 where

record Inner (A : Set) : Set where
  field inner : A
open Inner {{...}}

record Outer (A : Set) : Set where
  field {{outer}} : Inner A
open Outer {{...}}

module InstanceFieldUnderExplicitAndInstance
    (X : Set) (Y : Set) {{_ : Inner Y}} (F : X → Set) (G : (x : X) → {{Inner Y}} -> Outer (F x)) where

  test : ∀ x → F x
  test x = inner
