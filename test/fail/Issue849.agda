-- {-# OPTIONS -v tc.cover.cover:10 -v tc.cover.strategy:20 -v tc.cover.splittree:100 #-}
-- Andreas, 2013-05-15 Reported by jesper.cockx
module Issue849 where

data Bool : Set where
  true false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true

data D : Bool → Set where
  d1 : (x : Bool) → D x
  d2 : (x : Bool) → D (¬ x)

data ⊥ : Set where

data Test : (x : Bool) → (y : D x) → Set where
  c1 : (x : Bool)   → Test x (d1 x)
  c2 : (y : D true) → Test true y

-- WAS: The following function passes the coverage checker
-- even though the case for "f false (d2 true)" is not covered.
f : (x : Bool) → (y : D x) → Test x y
f x      (d1 .x) = c1 x
f true   y       = c2 y

impossible : Test false (d2 true) → ⊥
impossible ()

error : ⊥
error = impossible (f false (d2 true))

