{-# OPTIONS --no-syntax-based-termination #-}
{-# OPTIONS --type-based-termination #-}
{-# OPTIONS --sized-types #-}

-- Andreas, 2024-05-16, AIM XXXVIII, issue #7279
-- Internal error in TBT.

module TypeBasedTermination.HoTTCompatibleWithSizeBasedTerminationMaximeDenes where

open import Agda.Builtin.Size
open import Agda.Builtin.Equality

data Empty : Set where

data Box : Size → Set where
  wrap : ∀ i → (Empty → Box i) → Box (↑ i)

-- Box is inhabited at each stage > 0:

gift : ∀ {i} → Empty → Box i
gift ()

box : ∀ {i} → Box (↑ i)
box {i} = wrap i (gift {i})

-- wrap has an inverse:

unwrap : ∀ i → Box (↑ i) → (Empty → Box i)
unwrap .i (wrap i f) = f

-- There is an isomorphism between (Empty → Box ∞) and (Box ∞)
-- but none between (Empty → Box i) and (Box i).
-- We only get the following, but it is not sufficient to
-- produce the loop.

postulate iso : ∀ i → (Empty → Box i) ≡ Box (↑ i)

-- Since Agda's termination checker uses the structural order
-- in addition to sized types, we need to conceal the subterm.

postulate
  conceal : {A : Set} → A → A

mutual
  loop : ∀ i → Box i → Empty
  loop .(↑ i) (wrap i x) = loop' (↑ i) (Empty → Box i) (iso i) (conceal x)

  -- We would like to write  loop' i  instead of  loop' (↑ i)
  -- but this is ill-typed.  Thus, we cannot achieve something
  -- well-founded wrt. to sized types.

  loop' : ∀ i A → A ≡ Box i → A → Empty
  loop' i .(Box i) refl x = loop i x

-- The termination checker complains here, rightfully!

bug : Empty
bug = loop ∞ box
