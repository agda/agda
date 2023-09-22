-- Andreas, 2014-01-16, issue 1406
-- Agda with K again is inconsistent with classical logic

-- {-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --large-indices #-}

open import Common.Level
open import Common.Prelude
open import Common.Equality

cast : {A B : Set} (p : A ≡ B) (a : A) → B
cast refl a = a

data HEq {α} {A : Set α} (a : A) : {B : Set α} (b : B) → Set (lsuc α) where
  refl : HEq a a

mkHet : {A B : Set} (eq : A ≡ B) (a : A) → HEq a (cast eq a)
mkHet refl a = refl

-- Type with a big forced index. (Allowed unless --cubical-compatible.)
-- This definition is allowed in Agda master since 2014-10-17
-- https://github.com/agda/agda/commit/9a4ebdd372dc0510e2d77e726fb0f4e6f56781e8
-- However, probably the consequences of this new feature have not
-- been grasped fully yet.

data SING : (F : Set → Set) → Set where
  sing : (F : Set → Set) → SING F

-- The following theorem is the culprit.
-- It needs K.
-- It allows us to unify forced indices, which I think is wrong.

thm : ∀{F G : Set → Set} (a : SING F) (b : SING G) (p : HEq a b) → F ≡ G
thm (sing F) (sing .F) refl = refl

-- Note that a direct matching fails, as it generates heterogeneous constraints.
--   thm a .a refl = refl
-- However, by matching on the constructor sing, the forced index
-- is exposed to unification.

-- As a consequence of thm,
-- SING is injective which it clearly should not be.

SING-inj : ∀ (F G : Set → Set) (p : SING F ≡ SING G) → F ≡ G
SING-inj F G p = thm (sing F) _ (mkHet p (sing F))

-- The rest is an adaption of Chung-Kil Hur's proof (2010)

data Either {α} (A B : Set α) : Set α where
  inl : A → Either A B
  inr : B → Either A B

data Inv (A : Set) : Set1 where
  inv : (F : Set → Set) (eq : SING F ≡ A) → Inv A

¬ : ∀{α} → Set α → Set α
¬ A = A → ⊥

-- Classical logic

postulate em : ∀{α} (A : Set α) → Either A (¬ A)

Cantor' : (A : Set) → Either (Inv A) (¬ (Inv A)) → Set
Cantor' A (inl (inv F eq)) = ¬ (F A)
Cantor' A (inr _)          = ⊤

Cantor : Set → Set
Cantor A = Cantor' A (em (Inv A))

C : Set
C = SING Cantor

ic : Inv C
ic = inv Cantor refl

cast' : ∀{F G} → SING F ≡ SING G → ¬ (F C) → ¬ (G C)
cast' eq = subst (λ F → ¬ (F C)) (SING-inj _ _ eq)

-- Self application 1
diag : ¬ (Cantor C)
diag c with em (Inv C)  | c
diag c | inl (inv F eq) | c' = cast' eq c' c
diag _ | inr f          | _  = f ic

-- Self application 2
diag' : Cantor C
diag' with em (Inv C)
diag' | inl (inv F eq) = cast' (sym eq) diag
diag' | inr _          = _

absurd : ⊥
absurd = diag diag'
