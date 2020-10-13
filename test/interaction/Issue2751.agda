-- Andreas, 2017-10-06, issue #2751
-- Highlighting for unsolved constraints

module _ where

open import Agda.Builtin.Size

module UnsolvedSizeConstraints where

  mutual

    data D (i : Size) (A : Set) : Set where
      c : D′ i A → D i A

    record D′ (i : Size) (A : Set) : Set where
      inductive
      field
        size  : Size< i
        force : D size A

  open D′

  Map : (F : Set → Set) → Set₁
  Map F = {A B : Set} → F A → F B

  mutual

      map-D : ∀ {i} → Map (D i)
      map-D (c xs) = c (map-D′ xs)

      map-D′ : ∀ {i} → Map (D′ i)
      size  (map-D′ {i} t) = foo where postulate foo : Size< i
      force (map-D′ {i} t) = map-D {i = i} (force t)  -- correct is  i = foo

  -- Produces an unsolved size constraint.
  -- Problem WAS: no highlighting for unsolved constraints.
  -- Now: yellow highlighting in last rhs.

-- Test also highlighting for unsolved level constraints:

module UnsolvedLevelConstraints where

mutual
  l = _

  data D {a} (A : Set a) : Set l where
    c : A → D A  -- highlighted

  data E (A : Set l) : Set1 where
    c : A → E A  -- highlighted
