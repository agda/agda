{-# OPTIONS --guardedness-preserving-type-constructors #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Strict

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

D : Set
D = Rec (♯ (∞ D))

d : D
d = fold (♯ d)

postulate
  returnIO : ∀ {a} {A : Set a} → A → IO A

{-# COMPILE GHC returnIO = \_ _ -> return #-}

main : IO ⊤
main = primForce d (λ _ → returnIO tt)
