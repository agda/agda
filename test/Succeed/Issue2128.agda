
postulate
  A : Set
  I : ..(_ : A) → Set
  R : A → Set
  f : ∀ ..(x : A) (r : R x) → I x
 -- can now be used here ^
