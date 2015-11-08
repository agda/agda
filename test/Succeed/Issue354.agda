
-- {-# OPTIONS -v tc.conv:30 -v tc.conv.level:60 -v tc.meta.assign:15 #-}

module Issue354 where

open import Common.Level

------------------------------------------------------------------------
-- Preliminaries

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

_≗_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set (a ⊔ b)
f ≗ g = ∀ x → f x ≡ g x

------------------------------------------------------------------------
-- Example

postulate
  a     : Level
  A     : Set a
  P     : A → Set
  x     : A
  f     : ∀ {a} {A : Set a} → A → A
  g     : A → A
  lemma : f ≗ g

p : f x ≡ g x
p with f x | lemma x
... | .(g x) | refl = refl

-- The code above fails to type check, even though lemma x has the
-- type f x ≡ g x. However, if A is given the type Set zero, then the
-- code checks.

-- Excerpt from agda -vtc.with:100 --show-implicit Bug.agda:
--
--   checkWithFunction
--     delta1 =
--     delta2 =
--     gamma  =
--     as     = [A, _≡_ {a} {A} (f {a ⊔ a} {A} x) (g x)]
--     vs     = [f {a} {A} x, lemma x]
--     b      = _≡_ {a} {A} (f {a} {A} x) (g x)
--     qs     = []
--     perm   =  ->
--
-- Notice the occurrence of a ⊔ a.
