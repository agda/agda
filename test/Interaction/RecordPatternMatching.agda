module RecordPatternMatching where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

data Unit : Set where
  unit : Unit

foo : Unit × Unit → Unit
foo (x , y) = {!!}

record Box (A : Set) : Set where
  constructor [_]
  field
    proj : A

bar : Box Unit → Unit
bar [ x ] = {!!}
