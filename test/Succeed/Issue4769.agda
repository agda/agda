-- Andreas, 2020-06-21, issue #4769
-- Name and hiding ignored in subsequent face constraint patterns.
-- Instead, we should throw a warning.

open import Agda.Primitive.Cubical

data S : Set where
  base : S

foo : ∀ i j → Partial _ S
foo i j (i = i0) {{agdaDoesNotSeeThisName = (j = i1)}} = base

-- Expect: warning about name and "instance" flavor and argument.
