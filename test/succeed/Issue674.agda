-- Andreas 2012-07-07
module Issue674 where

record unit : Set where
  constructor tt

module A ⦃ t : unit ⦄ (i : unit) where
  id : unit → unit
  id x = x


open A {{t = _}} tt

module N = A {{ tt }} tt
open N

open A {{tt}} tt

module M = A tt
open M

open A tt
-- the last statement caused a panic when inserting the instance meta
-- because due to open it found candidates in scope that were not
-- in the signature yet
