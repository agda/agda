-- 2014-07-30 Andreas, issue reported by toporoskyy.y

data Nat : Set where
   Zero : Nat
   Succ : Nat -> Nat

boom : Nat -> Nat
boom n@(Succ _) = Zero

-- EXPECTED:
-- Not supported: @-patterns
-- when scope checking the left-hand side boom n@(Succ _) in the
-- definition of boom
