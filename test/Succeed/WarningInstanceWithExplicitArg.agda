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
