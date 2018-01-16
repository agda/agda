open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Strict

data D : Set where
  c : ∞ D → D

d : D
d = c (♯ d)

postulate
  returnIO : ∀ {a} {A : Set a} → A → IO A

{-# COMPILE GHC returnIO = \_ _ -> return #-}

main : IO ⊤
main = primForce d (λ _ → returnIO tt)
