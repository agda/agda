{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

-- Now we're getting somewhere! Inductive families of datatypes.

module Families where

-- You can import modules defined in other files.
-- More details later...
open import Nat

-- Think of an inductive family...

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 40 _::_

-- Some simple functions
head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: _) = x  -- no need for a [] case

-- Does the definition look familiar?
map : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
map f []        = []
map f (x :: xs) = f x :: map f xs

infixr 40 _++_

_++_ : {A : Set}{n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- Why does this type check? Let's walk through it slowly.
-- When pattern matching on the first vector, n is instantiated.

-- What happens if we make the lengths explicit?

cat : {A : Set}(n m : Nat) -> Vec A n -> Vec A m -> Vec A (n + m)
cat .zero    m []              ys = ys
cat .(suc n) m (_::_ {n} x xs) ys = x :: (cat n m xs ys)

-- Patterns which get instantiated by pattern matching on other stuff
-- get tagged by a dot. If you erase all the dotted things you get a
-- well-formed linear first-order pattern.

-- Inside the dot we could have arbitrary terms. For instance,

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

-- Let's do some other interesting families.

-- The identity type.
data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

infix 30 _==_ _!=_
infix 20 ¬_

-- In the presence of families we get a lot more empty types.

data Bool : Set where
  true  : Bool
  false : Bool

data False : Set where

¬_ : Set -> Set
¬ A = A -> False

_≠_ : {A : Set} -> A -> A -> Set
x ≠ y = ¬ x == y

true≠false : true == false -> False -- true ≠ false
true≠false ()

lem : (n : Nat) -> n == suc n -> False
lem n ()

-- Why does this work: true == false is an empty type.

{-

  What's next?

-}

-- Actually, inductive families are sufficiently fun that
-- you'll never get bored, but there's even more fun to be had.

-- Move on to: With.agda
