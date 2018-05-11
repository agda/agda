module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

record Category {o h} : Set (lsuc (o ⊔ h)) where
  no-eta-equality
  constructor con

  field
    Obj : Set o
    Hom : Obj → Obj → Set h

  field
    id : ∀ {X : Obj} → Hom X X
    comp : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    id-left : ∀ {X Y} (f : Hom X Y) → comp id f ≡ f

open Category

postulate
  isSet : ∀ {l} → (X : Set l) → Set l

hSets : (o : Level) → Category
hSets o .Obj                 = Σ (Set o) isSet
hSets o .Hom (A , _) (B , _) = A → B
hSets o .id                  = \ x → x
hSets o .comp f g            = \ x → f (g x)
hSets o .id-left f           = refl
