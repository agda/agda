-- Andreas, 2016-07-25, issue #2108
-- test case and report by Jesper

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.pos.occ:70 #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

lone = lsuc lzero

record Level-zero-or-one : Set where
  field
    level : Level
    is-lower : (level ⊔ lone) ≡ lone

open Level-zero-or-one public

Coerce : ∀ {a} → a ≡ lone → Set₁
Coerce refl = Set

data Test : Set₁ where
  test : Coerce (is-lower _) → Test

-- WAS:
-- Meta variable here triggers internal error.

-- Should succeed with unsolved metas.
