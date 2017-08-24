
open import Agda.Primitive

infixr 5 _,_
postulate
  Pair : ∀ {a} (A : Set a) {b} (B : Set b) → Set (a ⊔ b)
  _,_  : ∀ {a} {A : Set a} {b} {B : Set b} → A → B → Pair A B

-- If we turn Contraint, mkConstraint into postulate
-- we get "Failed to solve ... constraints" instead.

data Constraint {a} {A : Set a} (x : A) : Set where
  mkConstraint : Constraint x

postulate
  Inner : ∀ {l a b} {A : Set a} {B : Set b} (x : A) (y : B) → Constraint x → Set l → Set l

record Inner' {l a b c} {A : Set a} {B : Set b} {C : Set c} (x : A) (y : B) (z : C)
              (_ : Constraint (x , y , z)) (X : Set l) : Set l where
  -- no-eta-equality  -- With no-eta we get "No instance" error
  field
    value : X

Class : ∀ {l a b} {A : Set a} {B : Set b} (x : A) (y : B) (X : Set l) → Set l
Class x y X = Inner x y mkConstraint X

Class' : ∀ {l a b c} {A : Set a} {B : Set b} {C : Set c} (x : A) (y : B) (z : C) (X : Set l) → Set l
Class' x y z X = Inner' x y z mkConstraint X

postulate
  I : Set

-- If we make A and mkA postulates, we get the "No instance" error instead
data A a : (x : I) → Set a where
  mkA : (x : I) → A a x

-- If we turn B and fld into postulates, we get the "No instance" error
record B : Set1 where
  field fld : Set
open B

postulate
  a   : Level
  toB : (x : I) → A a x → B

postulate
  instance
    iToUnindexed : ∀
      {B   : I → Set1}
      {toB : ∀ (x : I) → A a x → B x}
      {B?  : ∀ (x : I) → B x → Set}
      {{_ : Class toB B? (∀ x → B? x (toB x (mkA x)))}}
      {x : I} → Class' (mkA x) (toB x) (B? x) (B? x (toB x (mkA x)))

    iIndexedAB : Class toB (λ _ → fld) (∀ x → fld (toB x (mkA x)))

it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x

goal =
  let i = _
      I : Set i
      I = A _ _
      A : I → Set
      A = _
      B : I → Set
      B = _
      x : I
      x = mkA _
  in it {A = Class' x A B (A x → B x)}

-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:95
