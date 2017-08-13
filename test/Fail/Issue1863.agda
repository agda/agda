-- Jesper, 2017-08-13: This test case now fails since instantiation
-- of metavariables during case splitting was disabled (see #2621).

{-# OPTIONS --allow-unsolved-metas #-}

record ⊤ : Set where
  constructor tt

data I : Set where
  i : ⊤ → I

data D : I → Set where
  d : D (i tt)

postulate
  P : (x : I) → D x → Set

foo : (y : _) → P _ y
foo d = {!!}
