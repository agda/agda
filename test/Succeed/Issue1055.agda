-- 2014-04-06 Andreas, issue reported by Andres Sicard-Ramirez

-- {-# OPTIONS --termination-depth=100 -v term.matrices:40 #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- The following function is accepted by the termination checker in
-- Agda-2.3.2.2, but it is rejected by the termination checker in
-- the current development version. (The function was adapted from Lee,
-- Jones, and Ben-Amram, POPL '01).
p : ℕ → ℕ → ℕ → ℕ
p m n        (succ r) = p m r n
p m (succ n) zero     = p zero n m
p m zero     zero     = m

