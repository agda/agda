-- Andreas, 2016-06-03, bug found by Ulf
-- {-# OPTIONS -v tc.cover:20 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst
open Σ

record ⊤ : Set where
data ⊥ : Set where

T : Bool → Set
T true = ⊤
T false = ⊥

p : Σ Bool T
fst p = false
p = true , _

loop : ⊥
loop = snd p
