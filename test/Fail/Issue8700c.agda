{-# OPTIONS --safe --cubical #-}

-- Issue found by Claude and reported by bdrisc-ant on Github

-- Cubical variant: the clause matcher treats any properly applied
-- primHComp as matchable "regardless of blocking", so an hcomp in Bool with
-- an *open* base x is a definite mismatch against the pattern  true  and the
-- catch-all second clause fires while f's last clause is being checked.
-- That mismatch is not stable: at x = true the hcomp computes to true and
-- the completed f answers by its first clause, so  M.bad true : true ≡ false.
-- (No hcomp clause is generated for Bool; for the HIT case see ...HCompHIT.)

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_;
            primHComp to hcomp; primTransp to transp; itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Bool

data ⊥ : Type where
record ⊤ : Type where
  constructor tt

f : Bool → Bool → Bool
f true  _     = true
f x     true  = false
f false false = false
  module M where
    -- Checked when only the first two clauses of f are in the signature.
    bad : (x : Bool) → f (hcomp {φ = i0} (λ _ → isOneEmpty) x) true ≡ false
    bad x = λ _ → false

boom : true ≡ false
boom = M.bad true

T : Bool → Type
T true  = ⊤
T false = ⊥

-- (Extraction through a variable path, so that  T (p i0)  reduces by the
-- endpoint rule on both the fast and the slow reducer.)
coerce : true ≡ false → ⊤ → ⊥
coerce p x = transp (λ i → T (p i)) i0 x

absurd : ⊥
absurd = coerce boom tt
