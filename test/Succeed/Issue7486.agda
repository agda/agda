module Issue7486 where

open import Agda.Builtin.Bool

postulate
  A B : Set

F : Bool → Set
F true = A
F false = B

-- Passing program which relies on the instance table treating `i` as an
-- instance 'for any class', allowing the conversion checker to, at each
-- of the use cases below, invert F and solve `it`.
--
-- Pre 2.7.0, was: `i` is never tried because the head `Def` in its type
-- is `F`, and we're never ever looking for an instance "of `F`".

postulate
  instance i : {b : Bool} → F b

it : {A : Set} → {{A}} → A
it {{x}} = x

_ : A
_ = it

_ : B
_ = it
