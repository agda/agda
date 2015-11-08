module Issue790 where

open import Common.Level   renaming (lzero to zero; lsuc to suc)
open import Common.Prelude using (Bool; true; false; zero; suc) renaming (Nat to ℕ)

even? : ℕ -> Bool
even? 0             = true
even? (suc (suc n)) = even? n
even? _             = false

-- Name overlap between Level's suc and Nat's suc should not matter,
-- since only one is a constructor.
