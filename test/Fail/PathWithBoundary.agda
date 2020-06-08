{-# OPTIONS --cubical #-}
module PathWithBoundary where

open import Agda.Builtin.Cubical.Path

open import Agda.Builtin.Nat



pred : Nat → Nat
pred (suc n) = n
pred 0 = 0


-- if the with abstraction correcly propagates the boundary the second
-- clause will not typecheck.
false : ∀ n {m} → (pred n + m) ≡ m
false n {m} i with pred n
... | zero  = m
... | suc q = m
