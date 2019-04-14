-- Andreas, 2019-03-28, issue #3600
--
-- Problem WAS: The size conversion checker produced invalid
-- constraints when getting stuck during checking, e.g., a <= max b a'.
-- The failing attempt of a <= b would produce constraints, which is unsound.
-- Now, we fail hard if a <= b gets stuck; this gives us a chance to succeed
-- on a <= a' instead.

{-# OPTIONS --sized-types #-}
{-# OPTIONS --show-implicit #-}

-- {-# OPTIONS -v tc.conv.size:60 -v tc.conv:10 #-}
-- {-# OPTIONS -v tc.meta.assign:10 #-}

open import Agda.Builtin.Size

data Type : (i : Size) → Set where

  _⇒_  : ∀ {i j}
       → Type i
       → Type j
       → Type (↑ (i ⊔ˢ j))

  Unit : ∀ {i} → Type (↑ i)

data Ty : ∀ {i} → Type i → Set where

  _⇒_  : ∀ {i j} {A : Type i} {B : Type j}
       → Ty A
       → Ty B
       → Ty {↑ (i ⊔ˢ j)} (A ⇒ B)

  Arr  : ∀ {i j} {A : Type i} {B : Type j}
       → Ty A
       → Ty B
       → Ty (A ⇒ B)

-- Should succeed.
