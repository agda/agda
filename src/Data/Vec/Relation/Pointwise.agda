------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to vectors
------------------------------------------------------------------------

module Data.Vec.Relation.Pointwise where

open import Category.Functor
open import Data.Fin
open import Data.Nat
open import Data.Plus as Plus hiding (equivalent; map)
open import Data.Vec as Vec hiding ([_]; head; tail; map)
import Data.Vec.Properties as VecProp
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Equiv
  using (_⇔_; ⇔-setoid; module Equivalence)
import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

-- Functional definition.

record Pointwise {ℓ} {A B : Set ℓ} (_∼_ : REL A B ℓ)
                 {n} (xs : Vec A n) (ys : Vec B n) : Set ℓ where
  constructor ext
  field app : ∀ i → lookup i xs ∼ lookup i ys

-- Inductive definition.

infixr 5 _∷_

data Pointwise′ {ℓ} {A B : Set ℓ} (_∼_ : REL A B ℓ) :
                ∀ {n} (xs : Vec A n) (ys : Vec B n) → Set ℓ where
  []  : Pointwise′ _∼_ [] []
  _∷_ : ∀ {n x y} {xs : Vec A n} {ys : Vec B n}
        (x∼y : x ∼ y) (xs∼ys : Pointwise′ _∼_ xs ys) →
        Pointwise′ _∼_ (x ∷ xs) (y ∷ ys)

-- The two definitions are equivalent.

equivalent : ∀ {ℓ} {A B : Set ℓ} {_∼_ : REL A B ℓ} {n}
               {xs : Vec A n} {ys : Vec B n} →
             Pointwise _∼_ xs ys ⇔ Pointwise′ _∼_ xs ys
equivalent {A = A} {B} {_∼_} = Equiv.equivalence (to _ _) from
  where
  to : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
       Pointwise _∼_ xs ys → Pointwise′ _∼_ xs ys
  to []       []       xs∼ys = []
  to (x ∷ xs) (y ∷ ys) xs∼ys =
    Pointwise.app xs∼ys zero ∷
    to xs ys (ext (Pointwise.app xs∼ys ∘ suc))

  nil : Pointwise _∼_ [] []
  nil = ext λ()

  cons : ∀ {n x y} {xs : Vec A n} {ys : Vec B n} →
         x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (x ∷ xs) (y ∷ ys)
  cons {x = x} {y} {xs} {ys} x∼y xs∼ys = ext helper
    where
    helper : ∀ i → lookup i (x ∷ xs) ∼ lookup i (y ∷ ys)
    helper zero    = x∼y
    helper (suc i) = Pointwise.app xs∼ys i

  from : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
         Pointwise′ _∼_ xs ys → Pointwise _∼_ xs ys
  from []            = nil
  from (x∼y ∷ xs∼ys) = cons x∼y (from xs∼ys)

-- Some destructors.

head : ∀ {ℓ} {A B : Set ℓ} {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise′ _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
head (x∼y ∷ xs∼ys) = x∼y

tail : ∀ {ℓ} {A B : Set ℓ} {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise′ _∼_ (x ∷ xs) (y ∷ ys) → Pointwise′ _∼_ xs ys
tail (x∼y ∷ xs∼ys) = xs∼ys

-- Pointwise preserves reflexivity.

refl : ∀ {ℓ} {A : Set ℓ} {_∼_ : Rel A ℓ} {n} →
       Reflexive _∼_ → Reflexive (Pointwise _∼_ {n = n})
refl rfl = ext (λ _ → rfl)

-- Pointwise preserves symmetry.

sym : ∀ {ℓ} {A B : Set ℓ} {P : REL A B ℓ} {Q : REL B A ℓ} {n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {n = n})
sym sm xs∼ys = ext λ i → sm (Pointwise.app xs∼ys i)

-- Pointwise preserves transitivity.

trans : ∀ {ℓ} {A B C : Set ℓ}
          {P : REL A B ℓ} {Q : REL B C ℓ} {R : REL A C ℓ} {n} →
        Trans P Q R →
        Trans (Pointwise P) (Pointwise Q) (Pointwise R {n = n})
trans trns xs∼ys ys∼zs = ext λ i →
  trns (Pointwise.app xs∼ys i) (Pointwise.app ys∼zs i)

-- Pointwise preserves equivalences.

isEquivalence :
  ∀ {ℓ} {A : Set ℓ} {_∼_ : Rel A ℓ} {n} →
  IsEquivalence _∼_ → IsEquivalence (Pointwise _∼_ {n = n})
isEquivalence equiv = record
  { refl  = refl  (IsEquivalence.refl  equiv)
  ; sym   = sym   (IsEquivalence.sym   equiv)
  ; trans = trans (IsEquivalence.trans equiv)
  }

-- Pointwise preserves decidability.

decidable : ∀ {ℓ} {A B : Set ℓ} {_∼_ : REL A B ℓ} →
            Decidable _∼_ → ∀ {n} → Decidable (Pointwise _∼_ {n = n})
decidable {_∼_ = _∼_} dec xs ys =
  Dec.map (Setoid.sym (⇔-setoid _) equivalent) (decidable′ xs ys)
  where
  decidable′ : ∀ {n} → Decidable (Pointwise′ _∼_ {n = n})
  decidable′ []       []       = yes []
  decidable′ (x ∷ xs) (y ∷ ys) with dec x y
  ... | no ¬x∼y = no (¬x∼y ∘ head)
  ... | yes x∼y with decidable′ xs ys
  ...   | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
  ...   | yes xs∼ys = yes (x∼y ∷ xs∼ys)

-- Pointwise _≡_ is equivalent to _≡_.

Pointwise-≡ : ∀ {ℓ} {A : Set ℓ} {n} {xs ys : Vec A n} →
              Pointwise _≡_ xs ys ⇔ xs ≡ ys
Pointwise-≡ {ℓ} {A} =
  Equiv.equivalence
    (to ∘ _⟨$⟩_ {f₂ = ℓ} (Equivalence.to equivalent))
    (λ xs≡ys → P.subst (Pointwise _≡_ _) xs≡ys (refl P.refl))
  where
  to : ∀ {n} {xs ys : Vec A n} → Pointwise′ _≡_ xs ys → xs ≡ ys
  to []               = P.refl
  to (P.refl ∷ xs∼ys) = P.cong (_∷_ _) $ to xs∼ys

-- Pointwise and Plus commute when the underlying relation is
-- reflexive.

⁺∙⇒∙⁺ : ∀ {ℓ} {A : Set ℓ} {_∼_ : Rel A ℓ} {n} {xs ys : Vec A n} →
        Plus (Pointwise _∼_) xs ys → Pointwise (Plus _∼_) xs ys
⁺∙⇒∙⁺ [ ρ≈ρ′ ]             = ext (λ x → [ Pointwise.app ρ≈ρ′ x ])
⁺∙⇒∙⁺ (ρ ∼⁺⟨ ρ≈ρ′ ⟩ ρ′≈ρ″) =
  ext (λ x → _ ∼⁺⟨ Pointwise.app (⁺∙⇒∙⁺ ρ≈ρ′ ) x ⟩
                   Pointwise.app (⁺∙⇒∙⁺ ρ′≈ρ″) x)

∙⁺⇒⁺∙ : ∀ {ℓ} {A : Set ℓ} {_∼_ : Rel A ℓ} {n} {xs ys : Vec A n} →
        Reflexive _∼_ →
        Pointwise (Plus _∼_) xs ys → Plus (Pointwise _∼_) xs ys
∙⁺⇒⁺∙ {ℓ} {A} {_∼_} x∼x =
  Plus.map (_⟨$⟩_ {f₂ = ℓ} (Equivalence.from equivalent)) ∘
  helper ∘
  _⟨$⟩_ {f₂ = ℓ} (Equivalence.to equivalent)
  where
  helper : ∀ {n} {xs ys : Vec A n} →
           Pointwise′ (Plus _∼_) xs ys → Plus (Pointwise′ _∼_) xs ys
  helper []                                                  = [ [] ]
  helper (_∷_ {x = x} {y = y} {xs = xs} {ys = ys} x∼y xs∼ys) =
    x ∷ xs  ∼⁺⟨ Plus.map (λ x∼y   → x∼y ∷ xs∼xs) x∼y ⟩
    y ∷ xs  ∼⁺⟨ Plus.map (λ xs∼ys → x∼x ∷ xs∼ys) (helper xs∼ys) ⟩∎
    y ∷ ys  ∎
    where
    xs∼xs : Pointwise′ _∼_ xs xs
    xs∼xs = _⟨$⟩_ {f₂ = ℓ} (Equivalence.to equivalent) (refl x∼x)

-- Note that ∙⁺⇒⁺∙ cannot be defined if the requirement of reflexivity
-- is dropped.

private

 module Counterexample where

  data D : Set where
    i j x y z : D

  data _R_ : Rel D Level.zero where
    iRj : i R j
    xRy : x R y
    yRz : y R z

  xR⁺z : x [ _R_ ]⁺ z
  xR⁺z =
    x  ∼⁺⟨ [ xRy ] ⟩
    y  ∼⁺⟨ [ yRz ] ⟩∎
    z  ∎

  ix : Vec D 2
  ix = i ∷ x ∷ []

  jz : Vec D 2
  jz = j ∷ z ∷ []

  ix∙⁺jz : Pointwise′ (Plus _R_) ix jz
  ix∙⁺jz = [ iRj ] ∷ xR⁺z ∷ []

  ¬ix⁺∙jz : ¬ Plus′ (Pointwise′ _R_) ix jz
  ¬ix⁺∙jz [ iRj ∷ () ∷ [] ]
  ¬ix⁺∙jz ((iRj ∷ xRy ∷ []) ∷ [ () ∷ yRz ∷ [] ])
  ¬ix⁺∙jz ((iRj ∷ xRy ∷ []) ∷ (() ∷ yRz ∷ []) ∷ _)

  counterexample :
    ¬ (∀ {n} {xs ys : Vec D n} →
         Pointwise (Plus _R_) xs ys →
         Plus (Pointwise _R_) xs ys)
  counterexample ∙⁺⇒⁺∙ =
    ¬ix⁺∙jz (Equivalence.to Plus.equivalent ⟨$⟩
               Plus.map (_⟨$⟩_ (Equivalence.to equivalent))
                 (∙⁺⇒⁺∙ (Equivalence.from equivalent ⟨$⟩ ix∙⁺jz)))

-- Map.

map : ∀ {ℓ} {A : Set ℓ} {_R_ _R′_ : Rel A ℓ} {n} →
      _R_ ⇒ _R′_ → Pointwise _R_ ⇒ Pointwise _R′_ {n}
map R⇒R′ xsRys = ext λ i →
  R⇒R′ (Pointwise.app xsRys i)

-- A variant.

gmap : ∀ {ℓ} {A A′ : Set ℓ}
         {_R_ : Rel A ℓ} {_R′_ : Rel A′ ℓ} {f : A → A′} {n} →
       _R_ =[ f ]⇒ _R′_ →
       Pointwise _R_ =[ Vec.map {n = n} f ]⇒ Pointwise _R′_
gmap {_R′_ = _R′_} {f} R⇒R′ {i = xs} {j = ys} xsRys = ext λ i →
  let module M = Morphism (VecProp.lookup-functor-morphism i) in
  P.subst₂ _R′_ (P.sym $ M.op-<$> f xs)
                (P.sym $ M.op-<$> f ys)
                (R⇒R′ (Pointwise.app xsRys i))
