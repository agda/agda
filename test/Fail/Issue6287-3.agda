@0 A : Set₁
A = Set
  module M where
    record R : Set₂ where
      constructor c

-- The following code should not be accepted, because the constructor
-- M.c is erased.

_ : M.R
_ = _
