{-# OPTIONS --universe-polymorphism --allow-unsolved-metas #-}

module Issue209 where

postulate
  Level : Set
  zero : Level
  suc  : Level → Level
  _⊔_ : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x

data _≅_ {a} {A : Set a} (x : A) : ∀ {b} {B : Set b} → B → Set where
  refl : x ≅ x

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P x → P y
subst P refl p = p

lemma : ∀ {A} (P : A → Set) {x y} (eq : x ≡ y) z →
        subst P eq z ≅ z
lemma P refl z = refl

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Telescope.hs:51

-- The problematic call to reorderTel is
--   reorderTel tel3
-- in Agda.TypeChecking.Rules.LHS.Instantiate.