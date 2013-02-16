module Issue794 where

open import Common.Prelude
open import Common.MAlonzo

postulate A : Set

record R : Set where
  id : A → A
  id x = x
