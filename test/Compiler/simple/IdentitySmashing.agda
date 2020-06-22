-- {-# OPTIONS -v treeless.opt:20 #-}
   -- Andreas, 2019-05-07, #3732: cannot have treeless printout in golden value
   -- because it is different for the MAlonzo and JS versions now.

open import Agda.Builtin.Nat
open import Common.IO using (return)
open import Agda.Builtin.Unit

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

data Vec {a} (A : Set a) : ..(_ : Nat) → Set a where
  [] : Vec A 0
  _∷_ : ∀ ..{n} → A → Vec A n → Vec A (suc n)

-- We can't handle smashing this yet. Different backends might compile
-- datatypes differently so we can't guarantee representational
-- compatibility. Possible solution: handle datatype compilation in
-- treeless as well and be explicit about which datatypes compile to the
-- same representation.
vecToList : ∀ {a} {A : Set a} ..{n} → Vec A n → List A
vecToList []       = []
vecToList (x ∷ xs) = x ∷ vecToList xs

data Fin : ..(_ : Nat) → Set where
  zero : ∀ ..{n} → Fin (suc n)
  suc  : ∀ ..{n} → Fin n → Fin (suc n)

-- These should all compile to identity functions:

wk : ∀ ..{n} → Fin n → Fin (suc n)
wk  zero   = zero
wk (suc i) = suc (wk i)

wkN : ∀ ..{n m} → Fin n → Fin (n + m)
wkN  zero   = zero
wkN (suc i) = suc (wkN i)

wkN′ : ∀ m ..{n} → Fin n → Fin (m + n)
wkN′ zero i = i
wkN′ (suc m) i = wk (wkN′ m i)

vecPlusZero : ∀ {a} {A : Set a} ..{n} → Vec A n → Vec A (n + 0)
vecPlusZero [] = []
vecPlusZero (x ∷ xs) = x ∷ vecPlusZero xs

main = return tt
