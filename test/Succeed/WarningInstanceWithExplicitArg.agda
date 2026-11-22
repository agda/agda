-- Jesper, 2018-11-29: Instances with explicit arguments will never be
-- used, so declaring them should give a warning.

postulate
  X : Set
  instance _ : Set → X -- this should give a warning

it : {{_ : X}} → X
it {{x}} = x

-- OTOH, this is fine as the instance can be used inside the module
module _ (A : Set) where
  postulate instance instX : X

  test : X
  test = it

-- Andreas, 2020-01-29, issue #4360:
-- Such warnings should also be given for data and record constructors.

record R (A : Set) : Set where
  instance constructor r
  field
    a : A

data D (A : Set) : Set where
  instance c : A → D A

-- Andreas, 2026-11-22, re #7047
-- Also for binding and generalizable variables.

postulate
  F : {{Set → X}} → Set      -- warning
  G : {{_ : Set → X}} → Set  -- warning

variable
  {{var}} : Set → X          -- warning
