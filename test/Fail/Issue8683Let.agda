{-# OPTIONS --cubical --safe #-}

-- Andreas, 2026-08-25, issue #8683, variant without `with`.
-- The rhs of a pattern-matching `let` is elaborated in inference mode,
-- which used to skip the side conditions of the cubical primitives.

open import Agda.Primitive.Cubical renaming (primHComp to hcomp)
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

P : Set
P = Σ Nat (λ _ → Nat)

-- The hcomp's base (1 , 1) disagrees with its side (constantly (0 , 0))
-- on φ = j, so this must be rejected.
bad : I → Nat
bad j = let (w , _) = hcomp {A = P} {φ = j} (λ i _ → (0 , 0)) (1 , 1) in w
