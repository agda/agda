
module _ where

record Pair (A B : Set) : Set where
  field
    π₁ : A
    π₂ : B

open Pair

foo : {A B : Set} → Pair A B  → Pair A B
foo = λ { x → {!x!} }
{- Case splitting on x produces:
   foo = λ { record { π₁ = π₃ ; π₂ = π₃ } → ? }
   Repeated variables in pattern: π₃
-}
