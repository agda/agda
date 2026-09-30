-- Andreas, 2016-09-22, issue #2183, issue reported by Ulf

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module _ (n : Nat) where

  foo : (m : Nat) → n ≡ m → Nat
  foo m refl = {!m!}

-- Splitting on m fails currently, as it internally is .n
-- We may be doing something about this in the future.

-- 2018-05-11, Jesper: Fixed!
