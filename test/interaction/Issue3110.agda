
postulate
  Nat : Set
  Fin : Nat → Set
  Foo : (n : Nat) → Fin n → Set

private
 module M where

  generalize
    {n} : Nat
    {m} : Fin _

  postulate
    Bar : Foo n m → Set

open M public using (Bar)

generalize
  n : Nat
  m : Fin _
  l : Foo n m

before : Bar l
before n m l = {!C-c C-e!}

after : Bar l
after n m l = {!C-c C-e!}
