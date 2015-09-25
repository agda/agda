-- Andreas, 2013-02-21, example by Andres Sicard Ramirez
module Issue782 where

open import Common.Prelude renaming (zero toz; suc tos; Nat toℕ)

f : ℕ → ℕ
f z     = z
f (s n) = z
