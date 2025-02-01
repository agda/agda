{-# OPTIONS --keep-pattern-variables #-}

open import Agda.Builtin.Bool

data Box : Bool → Set where
  box : (x : Bool) → Box x

test : Box true → Set
test x = {! x  !}
