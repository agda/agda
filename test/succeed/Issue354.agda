
{-# OPTIONS --universe-polymorphism #-}

module Issue354 where

------------------------------------------------------------------------
-- Preliminaries

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

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
