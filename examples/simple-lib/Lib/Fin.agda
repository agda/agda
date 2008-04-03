
module Lib.Fin where

open import Lib.Nat
open import Lib.Bool
open import Lib.Id

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

fromNat : (n : Nat) -> Fin (suc n)
fromNat zero    = zero
fromNat (suc n) = suc (fromNat n)

toNat : {n : Nat} -> Fin n -> Nat
toNat zero    = zero
toNat (suc n) = suc (toNat n)

weaken : {n : Nat} -> Fin n -> Fin (suc n)
weaken zero    = zero
weaken (suc n) = suc (weaken n)

lem-toNat-weaken : forall {n} (i : Fin n) -> toNat i ≡ toNat (weaken i)
lem-toNat-weaken zero    = refl
lem-toNat-weaken (suc i) with toNat i | lem-toNat-weaken i
... | .(toNat (weaken i)) | refl = refl

lem-toNat-fromNat : (n : Nat) -> toNat (fromNat n) ≡ n
lem-toNat-fromNat zero = refl
lem-toNat-fromNat (suc n) with toNat (fromNat n) | lem-toNat-fromNat n
... | .n | refl = refl

finEq : {n : Nat} -> Fin n -> Fin n -> Bool
finEq  zero    zero   = true
finEq  zero   (suc _) = false
finEq (suc _)  zero   = false
finEq (suc i) (suc j) = finEq i j

-- A view telling you if a given element is the maximal one.
data MaxView {n : Nat} : Fin (suc n) -> Set where
  theMax : MaxView (fromNat n)
  notMax : (i : Fin n) -> MaxView (weaken i)

maxView : {n : Nat}(i : Fin (suc n)) -> MaxView i
maxView {zero} zero = theMax
maxView {zero} (suc ())
maxView {suc n} zero = notMax zero
maxView {suc n} (suc i) with maxView i
maxView {suc n} (suc .(fromNat n)) | theMax   = theMax
maxView {suc n} (suc .(weaken i))  | notMax i = notMax (suc i)
