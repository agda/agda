{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 30, 2007


                Hello Agda!

                Ulf Norell

-}

-- Now we're getting somewhere! Inductive families of datatypes.

module Families where

-- You can import modules defined in other files.
-- More details later...
open import Naturals

-- Think of an inductive family...
module Vec where

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

{-

  Wait a second.. what's really going on here?

  All the indices were conveniently implicit!

-}

-- Ok. Let's make the implicit stuff explicit.
module WhatsGoingOnHere? where

  open Vec using (Vec; []; _::_)

  -- Now what's this funny dot thing?
  map : {A B : Set}(n : Nat) -> (A -> B) -> Vec A n -> Vec B n
  map .zero    f []              = []
  map .(suc _) f (x :: xs) = f x :: map _ f xs

  -- Basically the dot means: inside is not a pattern at all but a
  -- term whose value is uniquely determined by type checking
  -- the actual pattern.

  -- In the cases above the types of the patterns
  --   [] and (_::_ {n} x xs)
  -- forces the first argument to be zero and suc n respectively.
  -- So, that's what we write.

  -- We could spend hours talking about this, but let's move on...

-- Let's do some other interesting families.

-- The identity type.
data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

infix 30 _==_
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

-- [The following example might have worked at AIM6, but it does not
-- work now, so I commented it out. /NAD]

-- lem : (n : Nat) -> n == suc n -> False
-- lem n ()

-- Why does this work: true == false is an empty type.

{-

  What's next?

-}

-- Actually, inductive families are sufficiently fun that
-- you'll never get bored, but there's even more fun to be had.

-- Move on to: With.agda
