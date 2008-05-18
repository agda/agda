
module Data.Rational where

import Data.Bool as Bool
import Data.Nat as Nat
import Data.Integer as Int

open Int renaming
            ( _*_  to _*'_
            ; _+_  to _+'_
            ; -_   to -'_
            ; _-_  to _-'_
            ; !_!  to !_!'
            ; _==_ to _=='_
            ; _≤_  to _≤'_
            ; _≥_  to _≥'_
            ; _>_  to _>'_
            ; _<_  to _<'_
            )
open Nat using (Nat; zero; suc)
open Bool

infix  40 _==_ _<_ _>_ _≤_ _≥_
infixl 60 _+_ _-_
infixl 70 _%'_ _%_ _/_ _*_
infixr 80 _^_
infix  90 -_

data Rational : Set where
  _%'_  : Int -> Int -> Rational

numerator : Rational -> Int
numerator (n %' d) = n

denominator : Rational -> Int
denominator (n %' d) = d

_%_ : Int -> Int -> Rational
neg n       % neg m = pos (suc n) % pos (suc m)
pos 0       % neg m = pos 0 %' pos 1
pos (suc n) % neg m = neg n % pos (suc m)
x           % y     = div x z %' div y z
  where
    z = gcd x y

fromInt : Int -> Rational
fromInt x = x %' pos 1

fromNat : Nat -> Rational
fromNat x = fromInt (pos x)

_+_ : Rational -> Rational -> Rational
(a %' b) + (c %' d) = (a *' d +' c *' b) % (b *' d)

-_ : Rational -> Rational
- (a %' b) = -' a %' b

_-_ : Rational -> Rational -> Rational
a - b = a + (- b)

_/_ : Rational -> Rational -> Rational
(a %' b) / (c %' d) = (a *' d) % (b *' c)

_*_ : Rational -> Rational -> Rational
(a %' b) * (c %' d) = (a *' c) % (b *' d)

recip : Rational -> Rational
recip (a %' b) = b %' a

_^_ : Rational -> Int -> Rational
q ^ neg n       = recip q ^ pos (suc n)
q ^ pos zero    = fromNat 1
q ^ pos (suc n) = q * q ^ pos n

!_! : Rational -> Rational
! a %' b ! = pos ! a !' %' pos ! b !' 

round : Rational -> Int
round (a %' b) = div (a +' div b (pos 2)) b

_==_ : Rational -> Rational -> Bool
(a %' b) == (c %' d) = a *' d ==' b *' c

_<_ : Rational -> Rational -> Bool
(a %' b) < (c %' d) = a *' d <' b *' c

_>_ : Rational -> Rational -> Bool
(a %' b) > (c %' d) = a *' d >' b *' c

_≤_ : Rational -> Rational -> Bool
(a %' b) ≤ (c %' d) = a *' d ≤' b *' c

_≥_ : Rational -> Rational -> Bool
(a %' b) ≥ (c %' d) = a *' d ≥' b *' c

max : Rational -> Rational -> Rational
max a b = if a < b then b else a

min : Rational -> Rational -> Rational
min a b = if a < b then a else b

