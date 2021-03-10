
data M : Set where
  m : (I : _) → (I → M) → M

-- inferred
-- m : (I : Set) → (I → M) → M
