
module Issue475 where

data Box (A : Set) : Set where
  box : A → Box A

postulate
  T : {A : Set} → A → Set

unbox : {A : Set} → Box A → A

data BoxT {A : Set}(b : Box A) : Set where
  boxT : T (unbox b) → BoxT b

-- Can't be projection-like since we've already used it in BoxT
unbox (box x) = x

postulate
  A : Set
  b : Box A

unboxT : BoxT b → T (unbox b)
unboxT (boxT p) = p
