module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality

data Wrap {a} (A : Set a) : Set a where
  wrap : A → Wrap A

data Unit (A : Set) : Set where
  unit : Unit A

record Functor {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

open Functor ⦃ ... ⦄

instance
  FunWrap : ∀ {a} → Functor {a} Wrap
  FunWrap .fmap f (wrap x) = wrap (f x)

  FunUnit : Functor Unit
  FunUnit .fmap f unit = unit

_=$=_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Functor F}} {x y : F A}
          (f : A → B) → x ≡ y → fmap f x ≡ fmap f y
f =$= refl = refl

postulate A : Set

wrap-refl : (x : A) → wrap x ≡ wrap x
wrap-refl x = refl

prf : (x : Wrap A) → wrap x ≡ wrap x
prf (wrap x) = wrap =$= wrap-refl x

-- Incomplete pattern matching when applying FunUnit
-- (Internal error at Reduce.Fast:1347)
