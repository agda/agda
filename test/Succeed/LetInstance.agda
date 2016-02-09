
module _ where

postulate
  C : Set → Set
  A : Set
  i : C A
  foo : {X : Set} {{_ : C X}} → X

bar : A
bar = let instance z = i in foo
