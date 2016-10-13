
module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (_==_ to _==N_; _<_ to _<N_)

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

open Eq {{...}}

record Ord (A : Set) : Set where
  constructor mkOrd
  field
    _<_ : A → A → Bool
    overlap {{eqA}} : Eq A

open Ord {{...}} hiding (eqA)

record Num (A : Set) : Set where
  constructor mkNum
  field
    fromNat : Nat → A
    overlap {{eqA}} : Eq A

open Num {{...}} hiding (eqA)

instance
  EqNat : Eq Nat
  _==_ {{EqNat}} = _==N_

  OrdNat : Ord Nat
  _<_ {{OrdNat}} = _<N_
  Ord.eqA OrdNat = EqNat

  NumNat : Num Nat
  fromNat {{NumNat}} n = n
  Num.eqA NumNat = EqNat

infixr 3 _||_
_||_ : Bool → Bool → Bool
true  || x = true
false || x = x

-- Here it will pick the eq dictionary from the Ord
leq3 : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
leq3 x = x == fromNat 3 || x < fromNat 3

open import Agda.Builtin.Equality

2<3 : true ≡ leq3 2
2<3 = refl

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

-- Check that you get the first shared dictionary

getShared : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → Eq A
getShared = it

itsOrd : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → getShared ≡ Ord.eqA OrdA
itsOrd = refl

-- Check that it also works if you pattern match on the dictionaries

leq3' : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
leq3' {{mkOrd _<_}} {{mkNum fromNat}} x = x == fromNat 3 || x < fromNat 3
