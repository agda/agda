
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- A function that requires call-by-need
f : Nat → Nat → Nat
f a 0       = a
f a (suc b) = f (a + a) b

even : Nat → Bool
even n = mod-helper 0 1 n 1 == 0

data ⊥ : Set where
record ⊤ : Set where

IsTrue : Bool → Set
IsTrue false = ⊥
IsTrue true  = ⊤

-- Previously we reverted to slow reduce in when positivity checking.
f-even : IsTrue (even (f 1 64))
f-even = _
