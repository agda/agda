-- Andreas, 2017-10-04, issue #2753, reported by nad

-- Here, late solving of size constraints, prevented assignment
-- of instance metas to their solutions, since the metaOccurs
-- check then had more information through meta instantiation
-- and saw the loop.

-- To solve this issue, we switch off the meta-occurs check
-- for instance metas.  Instance search termination responsiblity
-- rests already in the hand of the user.

-- {-# OPTIONS -v tc.instance:30 #-}
-- {-# OPTIONS -v tc.constr.solve:30 #-}
-- {-# OPTIONS -v tc.size.solve:30 #-}
-- {-# OPTIONS -v tc.meta.assign:10 #-}

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

-- Worked without sized types since instance search succeeds
-- then quicker (not having to wait on the size constraint solver).

-- postulate
--   Size : Set

-- Size<_ : Size → Set
-- Size< i = Size

mutual

  data D (i : Size) : Set where
    c : D′ i → D i

  data D′ (i : Size) : Set where
    box : (j : Size< i) → D j → D′ i

record Fun (A B : Set) : Set where
  field
    applyTo : A → B

open Fun ⦃ … ⦄ public

mutual

  instance

    r : ∀ {i} → Fun (D i) (D i)
    Fun.applyTo r (c y) = c (applyTo y)

    r′ : ∀ {i} → Fun (D′ i) (D′ i)
    Fun.applyTo r′ (box j e) = box j (applyTo e)

-- Andreas' analysis as put on the bug tracker:
--
-- @UlfNorell is correct: the metaOccurs check prevents the
-- solution. However, why does it work without the sized types then? The
-- meta-occurs check does not go into solutions of metas. Thus, in the
-- case without sized types, where instance search succeeds immediately
-- (solving the hidden argument i by the conversion check), we are lucky
-- enough to slip through the meta-occurs check. However, in the case
-- with sized types, instance search does not succeed immediately because
-- the constraint on size i does not give a solution for i
-- directly. After size solving, instance search is retried, but then
-- (when we solve the second instance variable), instantiateFull already
-- has put in the solution for the first instance variable. Thus, the
-- loop becomes apparent, and metaOccurs protests.
