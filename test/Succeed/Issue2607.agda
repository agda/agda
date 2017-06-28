
-- Record modules for no-eta records should not be irrelevant in
-- record even if all fields are irrelevant (cc #392).

open import Agda.Builtin.Equality

postulate A : Set

record Unit : Set where
  no-eta-equality
  postulate a : A

record Irr : Set where
  no-eta-equality
  field .unit : Unit
  postulate a : A

record Coind : Set where
  coinductive
  postulate a : A

typeOf : {A : Set} → A → Set
typeOf {A} _ = A

checkUnit : typeOf Unit.a ≡ (Unit → A)
checkUnit = refl

checkIrr : typeOf Irr.a ≡ (Irr → A)
checkIrr = refl

checkCoind : typeOf Coind.a ≡ (Coind → A)
checkCoind = refl
