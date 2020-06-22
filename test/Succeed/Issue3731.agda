-- Andreas, 2019-04-30, issue #3731
-- Compiler backend: Do not look for a main function if not the main module.

open import Agda.Builtin.Nat

module Issue3731 where
module M where
  module main where

  record R : Set where
    field
      main : Nat

  data Main : Set where
    main : Main

module N where
  data main : Set where

module O where
  record main : Set where

module P where
  postulate
    main : Nat

module Q where
  abstract
    main : Nat
    main = 1

main : Nat
main = 0
