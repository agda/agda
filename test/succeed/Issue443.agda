module Issue443 where

module M (A : Set) where
  record R : Set where
    field
      a : A

postulate
  A : Set
  I : A → Set
  i : (x : A) → I x
  r : M.R A

a = M.R.a A r

Foo : Set₁
Foo with i (M.R.a A r)
Foo | _ = Set
