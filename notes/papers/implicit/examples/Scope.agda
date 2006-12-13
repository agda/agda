
module Scope where

{-

  So this goes through (we don't actually check scope). But what could really
  go wrong? This actually isn't captured by the main theorem, since we're type
  checking multiple definitions. Maybe it should be strengthened.

  Still nothing _bad_ happens here. Could we get some weird circular thing?
  Probably not. The main reason to check scope is to be able to state soundness
  in a reasonable way. So maybe we shouldn't make a big deal of scope.

-}

id : _ -> _
id x = x

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

z = id zero

