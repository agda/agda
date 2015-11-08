-- Andreas, 2013-10-21
-- There was a bug in Rules/Builtin such that NATEQUALS' equations
-- would be checked at type Nat instead of Bool.
-- This bug surfaced only because of today's refactoring in Conversion,
-- because then I got a strange unsolved constraint  true == true : Nat.

module NatEquals where

import Common.Level

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

infix 40 _=?=_

_=?=_ : Nat -> Nat -> Bool
zero  =?= zero  = true
zero  =?= suc _ = false
suc _ =?= zero  = false
suc n =?= suc m = n =?= m

{-# BUILTIN NATEQUALS _=?=_ #-}
