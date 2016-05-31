
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data Nat+Bool : Set where
  nat  : Nat  → Nat+Bool
  bool : Bool → Nat+Bool

data P : Nat+Bool → Set where
  p : {x : Nat+Bool} → P x

mkBool : ∀ {n b} → P (nat n) → P (bool b)
mkBool {zero}  _ = p {bool _}
mkBool {suc _} _ = p {bool _}

f : {x : Nat+Bool} → P x
f = λ { {nat n}  → g
      ; {bool b} → mkBool g }
  where
    g : P _
    g = p

crash : f {bool true} ≡ p {bool true}
crash = refl
