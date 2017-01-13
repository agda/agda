-- Andreas, 2014-01-08, following Maxime Denes 2014-01-06

-- This file demonstrates that size-based termination does
-- not lead to incompatibility with HoTT.

{-# OPTIONS --sized-types #-}

open import Common.Size
open import Common.Equality

data Empty : Set where

data Box : Size → Set where
  wrap : ∀ i → (Empty → Box i) → Box (↑ i)

-- Box is inhabited at each stage > 0:

gift : ∀ {i} → Empty → Box i
gift ()

box : ∀ {i} → Box (↑ i)
box {i} = wrap i gift

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
