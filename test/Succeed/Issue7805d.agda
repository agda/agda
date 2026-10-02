module Issue7805d where

open import Agda.Builtin.Nat

f : Nat → Set₁
f 0 = ∀ {x : Set} → x → x
f _ = Set

record Foo : Set₁ where
  field
    foo : Nat
    bar : f foo

test : Foo
test = record where
  bar x = x
  foo = 0
