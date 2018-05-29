
module _ where

open import Agda.Builtin.Nat

module M (n : Nat) where

  postulate A : Set

module M₁ (m : Nat) where

  open module Mm = M m

  bar : M.A (m + 1)
  bar = m  -- Nat !=< M.A (m + 1)

-- postulate
--   n : Nat

-- foo : M.A n
-- foo = {!n!}
