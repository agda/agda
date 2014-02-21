module Issue888 (A : Set) where
-- Check that let-bound variables show up in "show context"

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

f : Set -> Set
f X = let Y : ℕ -> Set
          Y n = ℕ
          m : ℕ
          m = {!!}
      in {!!}
