-- Unexpected context for generalized type #3110
postulate
  Nat : Set
  Fin : Nat → Set
  Foo : (n : Nat) → Fin n → Set

private
 module M where

  variable
    n : Nat
    m : Fin _

  postulate
    Bar : Foo n m → Set

open M public using (Bar)

variable
  n : Nat
  m : Fin _
  l : Foo n m

before : Bar l
before {n} {m} {l} = {!C-c C-e!}

after : Bar l
after {n} {m} {l} = {!C-c C-e!}
