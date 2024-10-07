-- Andreas, 2024-10-04, issue #7529, test case by Anders Mörtberg
-- LevelUniv not (fully) integrated with Cubical Agda.

{-# OPTIONS --cubical --level-universe #-}

-- {-# OPTIONS -v cubical.prim.transpTel.error:20 #-}
-- {-# OPTIONS -v impossible:10 #-}

module _ where

open import Agda.Primitive renaming (Set to Type)

data _≡_ {l : Level} {X : Type l} : X → X → Type l where
  refl : {x : X} → x ≡ x

Jbased : {l : Level} {X : Type l} (x : X) (A : (y : X) → x ≡ y → Type l)
       → A x refl → (y : X) (r : x ≡ y) → A y r
Jbased x A b _ refl = b

-- Used to be an internal error.

-- Should succeed.
