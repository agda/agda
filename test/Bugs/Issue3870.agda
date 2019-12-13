
module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality

data Wrap {a} (A : Set a) : Set a where
  wrap : A → Wrap A

data Unit (A : Set) : Set where
  unit : Unit A

cast : ∀ {A B} → Unit A → Unit B
cast unit = unit

data Functor {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  mkFunctor : (∀ {A B} → (A → B) → F A → F B) → Functor F

fmap : ∀ {a b} {A B : Set a} {F : Set a → Set b} →
            Functor F → (A → B) → F A → F B
fmap (mkFunctor m) = m

FunUnit : Functor Unit
FunUnit = mkFunctor λ _ → cast

postulate
  P : ∀ {a} {A : Set a} → A → Set a
  A : Set

fmapType : ∀ {b} {B : Set} {F : Set → Set b} {x : F A} →
             Functor F → (A → B) → P x → Set _
fmapType {x = x} Fun f _ = P (fmap Fun f x)

postulate
  wrapP : ∀ {a} {A : Set a} (x : A) → P (wrap x)

mutual-block : Set₁

a : Level
a = _

X : Set → Set a
X = _

FunX : Functor X
FunX = mkFunctor _

-- Adds constraint:
--   fmapType FunX wrap (wrapP x) == P (wrap (wrap x))
--   P (fmap FunX wrap (wrap x)   == P (wrap (wrap x))
--   fmap FunX wrap (wrap x)      == wrap (wrap x)
--   ?0 wrap (wrap x)             == wrap (wrap x)
constr₁ : (x : _) → fmapType {x = _} FunX wrap (wrapP x) → P (wrap (wrap x))
constr₁ x p = p

constr₂ : P FunX → P FunUnit
constr₂ p = p

mutual-block = Set
