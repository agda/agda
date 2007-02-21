
-- There's something very strange going on with mutual and parameterised
-- modules.  Can't reproduce the bug... :(
module Mutual where

data True : Set where
  tt : True

data False : Set where

data _\/_ (A B : Set) : Set where
  inl : A -> A \/ B
  inr : B -> A \/ B

swap : {A B : Set} -> A \/ B -> B \/ A
swap (inl a) = inr a
swap (inr b) = inl b

module Foo (A : Set)(P : A -> Set) where

  Q : A -> A -> Set
  Q x y = P x \/ P y

mutual

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  Even : Nat -> Set
  Even zero = True
  Even (suc zero) = False
  Even (suc (suc n)) = Even n

  f : Nat -> Set
  f zero    = True
  f (suc n) = Q n (suc n)
    where
      open module F = Foo Nat Even

  g : (n : Nat) -> f n
  g zero = tt
  g (suc zero) = inl tt
  g (suc (suc n)) = swap (g (suc n))

