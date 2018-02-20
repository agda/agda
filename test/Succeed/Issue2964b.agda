open import Agda.Builtin.Bool

record ⊤ : Set where constructor tt
data   ⊥ : Set where

record Σ (A : Set) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst
open Σ

T : Bool → Set
T false = ⊥
T true  = ⊤

Foo : Bool → Set
Foo false = Bool → Bool
Foo true  = Σ Bool T

foo : (x : Bool) → Foo x
foo false x    = x
foo true  .fst = true
foo true  .snd = tt
