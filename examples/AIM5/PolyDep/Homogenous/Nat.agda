module Homogenous.Nat where

import PolyDepPrelude
open PolyDepPrelude using (zero; one; _::_; nil; right; left; pair; unit)

import Homogenous.Base

open Homogenous.Base using (Sig; T; Intro)

-- The code for natural numbers is [0 1]

codeNat : Sig
codeNat = zero :: (one :: nil)

iNat : Set
iNat = T codeNat

-- Short-hand notation for the normal Nat constructors

izero : iNat
izero = Intro (left unit)

isucc : iNat -> iNat
isucc = \(h : iNat) -> Intro (right (left (pair h unit)))
-- the pair with the dummy unit component comes from the 1-tuple
--   representation as A*()

ione : iNat
ione = isucc izero

{-
main : Set
main = {!!}
-}
