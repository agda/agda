postulate
  ℤ     : Set
  n     : ℤ
  +_ -_ : ℤ → ℤ

-- It should not be possible to combine distinct unrelated prefix
-- operators with each other.

rejected : ℤ
rejected = + - n
