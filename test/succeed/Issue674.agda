module Issue674 where

record unit : Set where
  constructor tt

module A ⦃ t : unit ⦄ (i : unit) where
  id : unit → unit
  id x = x


module N = A {{ tt }} tt
open N

open A {{tt}} tt

module M = A tt
open M

-- fails yet:
-- open A tt
