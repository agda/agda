-- Andreas, 2022-07-21, issue #5956, reported by kangrongji
-- Testcase by dolio

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

p : I → Type₁
p i = Glue Type (λ { (i = i0) → (Type , idEquiv _) })

P : Type ≡ Glue Type _
P i = p i

-- Used to crash when trying to reify an empty system to a
-- pattern lambda.  Now reified as absurd lambda.
-- Expected result: unsolved metas.
