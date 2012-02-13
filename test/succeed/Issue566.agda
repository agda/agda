
module Issue566 where

open import Common.Level using (Level; _⊔_)

data D (a : Level) (A : Set a) : Set a where
 d : D a A → D a A

P-level : (a : Level) (A : Set a) → D a A → Level
P-level a A (d x) = P-level a A x

P : (a : Level) (A : Set a) (x : D a A) → Set (P-level a A x)
P a A (d x) = P a A x

postulate
 a : Level
 E : (b : Level) → Set b → Set a → Set (a ⊔ b)
 Q : (A : Set a) → D a A → Set a
 e : (A : Set a) (x : D a A) → E (P-level a A x) (P a A x) (Q A x)
 A : Set a
 x : D a A

foo : E (P-level a A x) (P a A x) (Q A x)
foo = e _ _

-- Bug.agda:23,7-12
-- P-level a A x ⊔ a != P-level a A x ⊔ a of type Level
-- when checking that the expression e _ _ has type
-- E (P-level a A x) (P a A x) (Q A x)
