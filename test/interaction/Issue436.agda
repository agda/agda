-- Andreas, 2016-06-20
-- Issue #436 fixed by Ulf's instantiating parameters sprint
-- (Agda meeting April 2016 Strathclyde)

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

foo : {A : Set} (x y : A) -> x == y -> A
foo x y = \ { eq → {!eq!} } -- load and do C-c C-c in the shed

-- Should work now (and is justified by new semantics).
