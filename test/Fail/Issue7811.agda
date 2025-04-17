-- Andreas, 2025-04-17, issue #7811
-- Internal error in telePiPath.

{-# OPTIONS --cubical #-}

-- {-# OPTIONS -v tc.with.abstract:30 #-}
-- {-# OPTIONS -v tc.tel.path:40 #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Path

p : Set ≡ Set
p i with Set _
... | _ = Set

-- Expected error: [PathAbstractionFailed]
-- Path abstraction failed for type Set (lsuc (_3 (i = i))) → Set₁.
-- The type may be non-fibrant or its sort depends on an interval variable
-- when checking that the clause
-- p i with Set _
-- ... | _ = Set
-- has type Set ≡ Set
