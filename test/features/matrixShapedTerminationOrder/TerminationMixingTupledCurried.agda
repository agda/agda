module TerminationMixingTupledCurried where

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

good : Nat × Nat -> Nat -> Nat
good (succ x , y) z = good (x , succ y) (succ z)
good (x , succ y) z = good (x , y) x
good xy (succ z) = good xy z
good _ _ = zero

