-- test termination using structured orders

module TerminationTupledAckermann where

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

-- addition in tupled form

add : Nat × Nat -> Nat
add (zero   , m) = m
add (succ n , m) = succ (add (n , m))

-- ackermann in tupled form

ack : Nat × Nat -> Nat
ack (zero   , y)      = succ y
ack (succ x , zero)   = ack (x , succ zero)
ack (succ x , succ y) = ack (x , ack (succ x , y))
