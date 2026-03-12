module Issue8465.Lib where

open import Agda.Builtin.Nat public using ()
  renaming (Nat to ℕ)  -- This renaming should be the definition site of ℕ
