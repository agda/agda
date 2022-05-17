{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool

variable
  a p         : Level
  A           : Set a
  P           : A → Set p
  x y : A

refl : x ≡ x
refl {x = x} = λ _ → x



data Interval : Set where
  left right : Interval
  line : left ≡ right

h2 : Bool → Interval
h2 true = left
h2 false = right

-- `left` and `right` are distinct canonical forms,
-- so `h2 ? = left` imples `? = true`.
--
-- Added this test to make sure we do not always give up on
-- injectivity when targeting a HIT.
_ : h2 _ ≡ left
_ = refl
