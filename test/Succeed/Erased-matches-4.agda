-- The option --erased-matches=non-dependent enables erased matches
-- for non-indexed, single-constructor data types.

{-# OPTIONS --erased-matches=non-dependent #-}

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set
