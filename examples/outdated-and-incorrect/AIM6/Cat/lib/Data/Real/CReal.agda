
module Data.Real.CReal where

import Prelude
import Data.Bool
import Data.String
import Data.Real.Complete
import Data.Real.Base
import Data.Nat
import Data.Integer
import Data.Rational as Rational
import Data.Interval
import Data.Real.Gauge
import Data.Show
import Data.List
import Data.Tuple

open Prelude
open Data.Real.Base
open Data.Real.Complete
open Data.Integer using (Int; pos) renaming (_-_ to _-i_; _<_ to _<i_)
open Rational hiding (fromInt)
open Data.Bool
open Data.String
open Data.Interval
open Data.Real.Gauge
open Data.Nat using (Nat)
open Data.Tuple

data CReal : Set where
  cReal : Complete Base -> CReal

approx : CReal -> Complete Base
approx (cReal f) ε = f ε

inject : Base -> CReal
inject x = cReal (unit x)

data BoundedCReal : Set where
  _∈_ : CReal -> Interval Base -> BoundedCReal

around : CReal -> Int
around (cReal f) = round (f (pos 1 % pos 2))

integerInterval : CReal -> Interval Base
integerInterval f = [ i - fromNat 1 ▻ i + fromNat 1 ]
  where
    i = Rational.fromInt (around f)

compact : CReal -> BoundedCReal
compact x = x ∈ integerInterval x

choke : BoundedCReal -> CReal
choke (cReal x ∈ [ lb ▻ ub ]) = cReal f
  where
    f : Complete Base
    f ε = ! y < lb => lb
          ! ub < y => ub
          ! otherwise y
      where
        y = x ε

compress : Complete Base -> Complete Base
compress x ε = approxBase (x ε2) ε2
  where
    ε2 = ε / fromNat 2

mapCR : (Base ==> Base) -> CReal -> CReal
mapCR f (cReal x) = cReal $ mapC f (compress x)

mapCR2 : (Base ==> Base ==> Base) -> CReal -> CReal -> CReal
mapCR2 f (cReal x) (cReal y) = cReal $ mapC2 f (compress x) (compress y)

bindR : (Base ==> Complete Base) -> CReal -> CReal
bindR f (cReal x) = cReal $ bind f (compress x)

approxRange : CReal -> Gauge -> Interval Base
approxRange x ε = [ r - ε ▻ r + ε ]
  where
    r = approx x ε

-- non-terminates for 0
proveNonZeroFrom : Gauge -> CReal -> Base
proveNonZeroFrom g r =
  ! high < fromNat 0 => high
  ! fromNat 0 < low  => low
  ! otherwise           proveNonZeroFrom (g / fromNat 2) r
  where
    i    = approxRange r g
    low  = lowerBound i
    high = upperBound i

proveNonZero : CReal -> Base
proveNonZero = proveNonZeroFrom (fromNat 1)

-- Negation

negateCts : Base ==> Base
negateCts = uniformCts id -_

realNegate : CReal -> CReal
realNegate = mapCR negateCts

-- Addition

plusBaseCts : Base -> Base ==> Base
plusBaseCts a = uniformCts id (_+_ a)

plusCts : Base ==> Base ==> Base
plusCts = uniformCts id plusBaseCts

realPlus : CReal -> CReal -> CReal
realPlus = mapCR2 plusCts

realTranslate : Base -> CReal -> CReal
realTranslate a = mapCR (plusBaseCts a)

-- Multiplication

multBaseCts : Base -> Base ==> Base
multBaseCts (pos 0 %' _) = constCts (fromNat 0)
multBaseCts a            = uniformCts μ (_*_ a)
  where
    μ = \ε -> ε / ! a !

-- First argument must be ≠ 0
multCts : Base -> Base ==> Base ==> Base
multCts maxy = uniformCts μ multBaseCts
  where
    μ = \ε -> ε / maxy

realScale : Base -> CReal -> CReal
realScale a = mapCR (multBaseCts a)

bound : Interval Base -> Base
bound [ lb ▻ ub ] = max ub (- lb)

realMultBound : BoundedCReal -> CReal -> CReal
realMultBound bx @ (x ∈ i) y = mapCR2 (multCts b) y (choke bx)
  where
    b = bound i

realMult : CReal -> CReal -> CReal
realMult x y = realMultBound (compact x) y

-- Absolute value
absCts : Base ==> Base
absCts = uniformCts id !_!

realAbs : CReal -> CReal
realAbs = mapCR absCts

fromInt : Int -> CReal
fromInt x = inject (Rational.fromInt x)

fromRational : Rational -> CReal
fromRational = inject

-- Reciprocal

recipCts : Base -> Base ==> Base
recipCts nz = uniformCts μ f
  where
    f : Base -> Base
    f a = ! fromNat 0 ≤ nz => recip (max nz a)
          ! otherwise         recip (min a nz)

    μ = \ε -> ε * nz ^ pos 2

realRecipWitness : Base -> CReal -> CReal
realRecipWitness nz = mapCR (recipCts nz)

realRecip : CReal -> CReal
realRecip x = realRecipWitness (proveNonZero x) x

-- Exponentiation

intPowerCts : Gauge -> Int -> Base ==> Base
intPowerCts _ (pos 0) = constCts (fromNat 1)
intPowerCts maxx n = uniformCts μ (flip _^_ n)
  where
    μ = \ε -> ε / (Rational.fromInt n * maxx ^ (n -i pos 1))

realPowerIntBound : BoundedCReal -> Int -> CReal
realPowerIntBound bx @ (x ∈ i) n = mapCR (intPowerCts b n) (choke bx)
  where
    b = bound i

realPowerInt : CReal -> Int -> CReal
realPowerInt = realPowerIntBound ∘ compact

showReal : Nat -> CReal -> String
showReal n x =
  ! len ≤' n => sign ++ "0." ++ fromList (replicate (n -' len) '0') ++ s
  ! otherwise   sign ++ i ++ "." ++ f
  where
    open Data.Nat using () renaming
              ( _^_ to _^'_
              ; div to div'; mod to mod'
              ; _==_ to _=='_; _≤_ to _≤'_
              ; _-_ to _-'_
              )
    open Data.Show
    open Data.List hiding (_++_)
    open Data.Integer using () renaming (-_ to -i_)

    k = 10 ^' n
    m = around $ realScale (fromNat k) x
    m' = if m <i pos 0 then -i m else m
    s = showInt m'

    sign = if m <i pos 0 then "-" else ""

    len = length (toList s)

    p = splitAt (len -' n) $ toList s
    i = fromList $ fst p
    f = fromList $ snd p

