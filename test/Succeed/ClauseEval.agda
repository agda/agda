
module _ where

-- Check that previous clauses reduce in later ones

open import Agda.Builtin.Nat hiding (_==_)

record Σ (A : Set) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

open Σ

postulate
  T : Nat → Set
  mkT : ∀ n → T n

t5 : Σ Nat T
fst t5 = 5
snd t5 = mkT 5

-- Also with instance projections --

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool
    reflexive : ∀ x → true ≡ (x == x)

open Eq {{...}}

instance
  EqNat : Eq Nat
  _==_ {{EqNat}} zero    zero    = true
  _==_ {{EqNat}} zero    (suc y) = false
  _==_ {{EqNat}} (suc x) zero    = false
  _==_ {{EqNat}} (suc x) (suc y) = x == y
  reflexive {{EqNat}} zero = refl
  reflexive {{EqNat}} (suc x) rewrite reflexive x = refl
