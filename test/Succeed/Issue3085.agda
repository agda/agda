-- 2018-05-25, Reported by Sergei Meshveliani on the Agda list

open import Common.Prelude

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

f : List (Nat × Nat) → List (Nat × Nat)
f ps =
     map (\p → let (x , y) = p in (x , suc y))  ps
