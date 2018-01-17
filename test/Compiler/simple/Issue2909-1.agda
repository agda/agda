open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Strict

record Box (A : Set) : Set where
  field
    unbox : A

open Box public

record R : Set where
  coinductive
  field
    force : Box R

open R public

r : R
unbox (force r) = r

postulate
  returnIO : ∀ {a} {A : Set a} → A → IO A

{-# COMPILE GHC returnIO = \_ _ -> return #-}

main : IO ⊤
main = primForce r (λ _ → returnIO tt)
