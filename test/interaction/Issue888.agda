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

-- Issue 1112: dependent let-bindings

data Singleton : ℕ → Set where
  mkSingleton : (n : ℕ) -> Singleton n

g : ℕ -> ℕ
g x =
  let i = zero
      z = mkSingleton x
  in {!!}
