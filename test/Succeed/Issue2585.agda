-- Andreas, 2017-05-15, issue 2585, reported by Martin Stone Davis
-- Information about whether a function uses copatterns
-- needs to be added already while function is defines.
-- Otherwise, clauses might fail to check due to missing eta.

{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.Equality

record Super : Set₁ where
  eta-equality
  field
    set : Set

record Sub : Set₁ where
  eta-equality
  field
    super1 : Super
    super2 : Super
    super1=2 : super1 ≡ super2

postulate
  X : Set

works : Sub
works .Sub.super1 = record { set = X }
works .Sub.super2 .Super.set = X
works .Sub.super1=2 = refl

test : Sub
test .Sub.super1 .Super.set = X
test .Sub.super2 .Super.set = X
test .Sub.super1=2 = refl

-- Should pass
