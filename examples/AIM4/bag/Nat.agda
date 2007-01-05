
module Nat where

  import Prelude
  import Equiv
  import Datoid

  open Prelude
  open Equiv
  open Datoid

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  one : Nat
  one = suc zero

  _+_ : Nat -> Nat -> Nat
  zero  + n = n
  suc m + n = suc (m + n)

  private
    eqNat : Nat -> Nat -> Bool
    eqNat zero    zero    = True
    eqNat (suc m) (suc n) = eqNat m n
    eqNat _       _       = False

    refl' : (x : Nat) -> T (eqNat x x)
    refl' zero    = unit
    refl' (suc n) = refl' n

    sym' : (x y : Nat) -> T (eqNat x y) -> T (eqNat y x)
    sym' zero     zero     _     = unit
    sym' (suc n1) (suc n2) eq    = sym' n1 n2 eq
    sym' (suc _)  zero     wrong = wrong
    sym' zero     (suc _)  wrong = wrong

    trans' : (x y z : Nat) -> T (eqNat x y) -> T (eqNat y z) -> T (eqNat x z)
    trans' zero     _        zero     _     _     = unit
    trans' (suc n1) (suc n2) (suc n3) eq12  eq23  = trans' n1 n2 n3 eq12 eq23
    trans' zero     (suc _)  _        wrong _     = absurdElim wrong
    trans' _        zero     (suc _)  _     wrong = absurdElim wrong
    trans' (suc _)  zero     _        wrong _     = absurdElim wrong
    trans' _        (suc _)  zero     _     wrong = absurdElim wrong

  decidableEquiv : DecidableEquiv Nat
  decidableEquiv = decEquiv (equiv (T' eqNat) refl' sym' trans')
                            (boolFunctionsDecidable eqNat)

  natDatoid : Datoid
  natDatoid = datoid Nat decidableEquiv

