-- Andreas, 2023-10-22, issue #6930 raised with test case by Andrew Pitts.
--
-- Acc-induction is compatible with strict Prop.
-- That is, if we define Acc in Prop, we can eliminate it into other propositions.

{-# OPTIONS --prop #-}
{-# OPTIONS --sized-types #-}

module _ where

open import Agda.Primitive

-- Acc-recursion in types.
------------------------------------------------------------------------

module wf-Set {l : Level}{A : Set l}(R : A → A → Set l) where

  -- Accessibility predicate
  data Acc (x : A) : Set l where
    acc : (∀ y → R y x → Acc y) → Acc x

  -- Well-foundedness
  iswf : Set l
  iswf = ∀ x → Acc x

  -- Well-founded induction
  ind :
    {n : Level}
    (w : iswf)
    (B : A → Set n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    → -----------------------------------
    ∀ x → B x
  ind w B b x = Acc→B x (w x)
    where
    Acc→B : ∀ x → Acc x → B x
    Acc→B x (acc α) = b x (λ y r → Acc→B  y (α y r))

-- Acc-induction in Prop
------------------------------------------------------------------------

{- The following module checks with 2.6.3, but fails to check with 2.6.4
   emitting the message:

   "Termination checking failed for the following functions:
  Problematic calls:
   Acc→B y _"

and highlighting the last occurrence of Acc→B  -}

module wf-Prop {l : Level}{A : Set l}(R : A → A → Prop l) where

  -- Accessibility predicate
  data Acc (x : A) : Prop l where
    acc : (∀ y → R y x → Acc y) → Acc x

  -- Well-foundedness
  iswf : Prop l
  iswf = ∀ x → Acc x

  -- Well-founded induction
  ind :
    {n : Level}
    (_ : iswf)
    (B : A → Prop n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    → -----------------------------------
    ∀ x → B x
  ind w B b x = Acc→B x (w x)
    where
    Acc→B : ∀ x → Acc x → B x
    Acc→B x (acc α) = b x (λ y r → Acc→B  y (α y r))

-- Andreas: Justification of Acc-induction using sized types.
------------------------------------------------------------------------

module wf-Prop-Sized {l : Level}{A : Set l}(R : A → A → Prop l) where
  open import Agda.Builtin.Size

  -- Accessibility predicate
  data Acc (i : Size) (x : A) : Prop l where
    acc : (j : Size< i) (α : ∀ y → R y x → Acc j y) → Acc i x

  -- Well-foundedness
  iswf : Prop l
  iswf = ∀ x → Acc ∞ x

  -- Well-founded induction
  ind :
    {n : Level}
    (w : iswf)
    (B : A → Prop n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    → -----------------------------------
    ∀ x → B x
  ind w B b x = Acc→B ∞ x (w x)
    where
    Acc→B : ∀ i x → Acc i x → B x
    Acc→B i x (acc j α) = b x (λ y r → Acc→B j y (α y r))
