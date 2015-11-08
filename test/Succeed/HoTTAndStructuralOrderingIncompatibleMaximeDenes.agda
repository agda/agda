-- Andreas, 2014-01-08, following Maxime Denes 2014-01-06

-- This file demonstrates then incompatibility of the untyped
-- structural termination ordering with HoTT.

open import Common.Equality

data Empty : Set where

data Box : Set where
  wrap : (Empty → Box) → Box

-- Box is inhabited:

gift : Empty → Box
gift ()

box : Box
box = wrap gift

-- wrap has an inverse:

unwrap : Box → (Empty → Box)
unwrap (wrap f) = f

-- Thus, Box is isomorphic to (Empty → Box).
-- However, they cannot be propositionally equal,
-- as this leads to an inconsistency as follows:

postulate iso : (Empty → Box) ≡ Box

module Rewrite where

  loop : Box → Empty
  loop (wrap x) rewrite iso = loop x

-- rewrite is not to blame, we can do it with with:

module With where

  loop : Box → Empty
  loop (wrap x) with (Empty → Box) | iso
  ... | ._ | refl = loop x

-- with is not to be blamed either, we can desugar it:

module Aux where
 mutual
  loop : Box → Empty
  loop (wrap x) = loop' (Empty → Box) iso x

  loop' : ∀ A → A ≡ Box → A → Empty
  loop' .Box refl x = loop x

open Aux

bug : Empty
bug = loop box

-- Moral of the story: the termination checker should reject `loop'.

-- If the termination checker should be fixed in that way,
-- move this test case to test/fail.
