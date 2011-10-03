-- Andreas, 2011-10-02
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:20 #-}
module Issue483 where

data _≡_ (a : Set) : Set → Set where
  refl : a ≡ a

test : (P : .Set → Set) → 
  let X : .Set → Set
      X = _
  in  (x : Set) → X x ≡ P (P x)
test P x = refl 

{-  THE FOLLOWING COULD BE SOLVED IN THE SPECIFIC CASE, BUT NOT IN GENERAL 
postulate
  A : Set
  a : A
  f : .A → A

test2 : let X : .A → A
            X = _
        in (x : A) → X a ≡ f x
test2 x = refl
-- should solve as X = f
-- it was treated as X _ = f _ before with solution X = \ x -> f _ 
-- which eta-contracts to X = f

{- INSTEAD GIVES:
Cannot instantiate the metavariable _16 to f _ since it contains
the variable x which is not in scope of the metavariable
when checking that the expression refl has type _16 _ ≡ f _
-}
-}
