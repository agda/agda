-- Andreas, 2020-05-16, issue #4649
-- Allow --safe flag in -I mode

{-# OPTIONS --safe #-}

data Unit : Set where
  unit : Unit

test : Unit
test = {!!}
