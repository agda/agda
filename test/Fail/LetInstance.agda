
module _ where

postulate
  C : Set → Set
  A : Set
  i : C A
  foo : {X : Set} {{_ : C X}} → X

-- Let bindings need to be declared 'instance' to be eligible.
bar : A
bar = let z = i in foo
