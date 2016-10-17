{-# OPTIONS --allow-unsolved-metas #-}

record R : Set₁ where
  field
    A : Set
    f : A → A

record Double {a} (A : Set a) : Set a where
  field
    double : A → A

open Double {{...}}

-- Type error (incomplete patterns in Patterns.Match)
doubleR : Double R
R.A (double {{doubleR}} x)   = R.A x
R.f (double {{doubleR}} x) z = R.f x (R.f x z)

-- Internal error (incomplete patterns in Reduce.Fast)
doubleR₁ : Double R
R.A (double {{doubleR₁}} x)   = R.A x
R.f (double {{doubleR₁}} x) z = {!R.f x (R.f x z)!}
