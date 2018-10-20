
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Vars (A : Set) where
  variable
    x : A

data It {A : Set} : A → Set where
  it : ∀ x → It x

module Fixed where
  open Vars Nat
  ret : It x
  ret {x = x} = it x

module Param (A : Set) where
  open Vars A
  ret : It x
  ret {x = x} = it x

open Vars Nat

check : Param.ret Nat ≡ Fixed.ret {x = x}
check = refl

-- Check that you can let open as long as you don't use the variables
foo : (A : Set) (let open Vars A) (x : A) → x ≡ x
foo A x = refl
