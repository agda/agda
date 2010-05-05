module Long where

data Nat : Set where
  z : Nat
  s : (n : Nat) → Nat

data Exp : Set where
  val : (n : Nat) → Exp
  throw : Exp

data Maybe (A : Set) : Set where
  Just    : A → Maybe A
  Nothing : Maybe A

abstract

  s′ : Nat → Nat
  s′ = s

eval : Exp → Maybe Nat
eval (val n) = ?
eval throw   = ?

data D : Nat → Set where
  d : D z

foo : D {!!}
foo = {!!}

bar : D z
bar = {!!}

baz : Maybe {!!}
baz = {!!}
