-- Andreas, 2019-05-30, issue #3823
-- Named where module M should be in scope in rhs.
-- This enables to use it in expressions like record{M}.

-- Jesper, 2019-12-19, issue #4288
-- Moved to test/Fail because the fix caused a loop in the scope
-- checker.

open import Agda.Builtin.Equality

record R : Set₂ where
  field
    A : Set₁

r : R
r = record {M}
  module M where
    A = Set

-- ERROR WAS:
-- No module M in scope
-- when scope checking record { M }

test : r ≡ record {A = Set}
test = refl

-- Should succeed.

-- Should also work with module parameters.

s : Set₁ → R
s B = record {L}
  module L where
    A = B

-- With rewrite:

postulate
  B : Set
  a b : B
  a≡b : a ≡ b
  P : B → Set

record W : Set where
  field
    wrap : P b

w : P a → W
w p rewrite a≡b = record {N}
  module N where
    wrap = p

-- Should also succeed in the presence of `rewrite`.

module N' = N  -- See issue #3824.
