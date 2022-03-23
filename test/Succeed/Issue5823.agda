-- Andreas, 2022-03-11, issue #5823
-- Make sure we do not weaken the singleton detection too much by checking for loops.

open import Agda.Builtin.Nat

record ⊤ : Set where

record Wrap (A : Set) : Set where
  field unwrap : A

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B

-- A singleton record type with nestings of Wrap.

Singleton = (Wrap ⊤ × Wrap (Wrap ⊤)) × Wrap (Wrap (Wrap ⊤ × ⊤) × Wrap ⊤)

-- Agda should solve this meta:

unique : Singleton
unique = _

-- This is fine, even though we pass through 'Wrap' several times.
-- Passing already visited non-recursive records is fine!

mutual
  record S (n : Nat) : Set where
    inductive; eta-equality
    field inn : T n

  T : Nat → Set
  T zero = ⊤
  T (suc n) = T n × S n

-- S n is a eta singleton type for each n because it is terminating.

inh5 : S 5
inh5 = _
