-- Andreas, 2026-05-07, issue #8553
-- Report and test case by Carlos Tome

module Issue8553 where

it : {A : Set} ⦃ _ : A ⦄ → A
it ⦃ a ⦄ = a

-- A singleton type:
record C : Set where

record Q : Set where
  field
    -- This instance projection conflicts with the instance for C defined later
    instance
      ⦃ q ⦄ : C

instance
  iC : C
  iC = record {}

open Q ⦃...⦄ public
-- This brings the instance projection into scope unqualified.

c-C : C
c-C = it

-- There are several way to solve the instance meta of type C here.
-- They are all definitionally equal, due to eta.
-- The bug was that Agda dropped the good one (iC) and then failed
-- to proceed with the bad one (q) since there is no instance for Q.

-- Now instance search succeeds trivially since C is a singleton type.


-- We can also solve instance metas of singleton types
-- even without any instance terms around.

record E : Set where

e : E
e = it

-- This is rejected as instance search in general
-- rejects search in explicit function spaces.
-- f : E → E
-- f = it {A = E → E}
