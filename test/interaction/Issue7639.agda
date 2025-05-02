record R : Set₁ where
  constructor c
  field f : Set

impossible : R
impossible = let c x = c _ in  {!!}
