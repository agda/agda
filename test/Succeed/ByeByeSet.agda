-- 'Set' is no longer a keyword but a primitive defined in
-- 'Agda.Primitive'. It is imported by default but this can be
-- disabled with a flag:

{-# OPTIONS --no-import-sorts #-}

-- By importing Agda.Primitive explicitly we can rename 'Set' to
-- something else:
open import Agda.Primitive renaming (Set to Type)

-- Now 'Set' is no longer in scope:
-- test₁ = Set
-- Error message: Not in scope: Set

-- Instead it is now called 'Type'. Note that suffixed versions
-- 'Type₁', 'Type₂', ... work as expected, as does 'Type ℓ' for a
-- level 'ℓ'!
Foo : Type₁
Foo = Type

Bar : ∀ ℓ → Type (lsuc ℓ)
Bar ℓ = Type ℓ

-- We can now redefine Set however we want:
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

IsSet : ∀ {ℓ} → Type ℓ → Type ℓ
IsSet X = {x y : X} (p q : x ≡ y) → p ≡ q

Set : ∀ ℓ → Type (lsuc ℓ)
Set ℓ = Σ (Type ℓ) IsSet
