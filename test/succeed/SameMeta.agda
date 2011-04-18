-- Andreas, 2011-04-15
-- {-# OPTIONS -v tc.meta:20 #-}
module SameMeta where

infix 10 _≡_

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

infixr 5 _×_ _,_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

postulate A : Set

same : let X : A -> A -> A -> A × A
           X = _
       in {x y z : A} -> X x y y ≡ (x , y)
                       × X x x y ≡ X x y y
same = refl , refl
-- second equation triggers pruning of second variable of X
-- which makes the first equation linear and solvable