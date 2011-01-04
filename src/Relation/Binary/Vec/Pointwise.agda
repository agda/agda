------------------------------------------------------------------------
-- Pointwise lifting of relations to vectors
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Vec.Pointwise where

open import Category.Applicative.Indexed
open import Data.Fin
open import Data.Plus as Plus hiding (equivalent; map)
open import Data.Vec as Vec hiding ([_]; map)
import Data.Vec.Properties as VecProp
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Equiv
  using (_⇔_; module Equivalent)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

private
 module Dummy {a} {A : Set a} where

  -- Functional definition.

  record Pointwise (_∼_ : Rel A a) {n} (xs ys : Vec A n) : Set a where
    constructor ext
    field app : ∀ i → lookup i xs ∼ lookup i ys

  -- Inductive definition.

  infixr 5 _∷_

  data Pointwise′ (_∼_ : Rel A a) :
                  ∀ {n} (xs ys : Vec A n) → Set a where
    []  : Pointwise′ _∼_ [] []
    _∷_ : ∀ {n x y} {xs ys : Vec A n}
          (x∼y : x ∼ y) (xs∼ys : Pointwise′ _∼_ xs ys) →
          Pointwise′ _∼_ (x ∷ xs) (y ∷ ys)

  -- The two definitions are equivalent.

  equivalent : ∀ {_∼_ : Rel A a} {n} {xs ys : Vec A n} →
               Pointwise _∼_ xs ys ⇔ Pointwise′ _∼_ xs ys
  equivalent {_∼_} = Equiv.equivalent (to _ _) from
    where
    to : ∀ {n} (xs ys : Vec A n) →
         Pointwise _∼_ xs ys → Pointwise′ _∼_ xs ys
    to []       []       xs∼ys = []
    to (x ∷ xs) (y ∷ ys) xs∼ys =
      Pointwise.app xs∼ys zero ∷
      to xs ys (ext (Pointwise.app xs∼ys ∘ suc))

    nil : Pointwise _∼_ [] []
    nil = ext λ()

    cons : ∀ {n x y} {xs ys : Vec A n} →
           x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (x ∷ xs) (y ∷ ys)
    cons {x = x} {y} {xs} {ys} x∼y xs∼ys = ext helper
      where
      helper : ∀ i → lookup i (x ∷ xs) ∼ lookup i (y ∷ ys)
      helper zero    = x∼y
      helper (suc i) = Pointwise.app xs∼ys i

    from : ∀ {n} {xs ys : Vec A n} →
           Pointwise′ _∼_ xs ys → Pointwise _∼_ xs ys
    from []            = nil
    from (x∼y ∷ xs∼ys) = cons x∼y (from xs∼ys)

  -- Pointwise preserves reflexivity.

  refl : ∀ {_∼_ : Rel A a} {n} →
         Reflexive _∼_ → Reflexive (Pointwise _∼_ {n = n})
  refl rfl = ext (λ _ → rfl)

  -- Pointwise preserves symmetry.

  sym : ∀ {_∼_ : Rel A a} {n} →
        Symmetric _∼_ → Symmetric (Pointwise _∼_ {n = n})
  sym sm xs∼ys = ext λ i → sm (Pointwise.app xs∼ys i)

  -- Pointwise preserves transitivity.

  trans : ∀ {_∼_ : Rel A a} {n} →
        Transitive _∼_ → Transitive (Pointwise _∼_ {n = n})
  trans trns xs∼ys ys∼zs = ext λ i →
    trns (Pointwise.app xs∼ys i) (Pointwise.app ys∼zs i)

  -- Pointwise preserves equivalences.

  isEquivalence :
    ∀ {_∼_ : Rel A a} {n} →
    IsEquivalence _∼_ → IsEquivalence (Pointwise _∼_ {n = n})
  isEquivalence equiv = record
    { refl  = refl  (IsEquivalence.refl  equiv)
    ; sym   = sym   (IsEquivalence.sym   equiv)
    ; trans = trans (IsEquivalence.trans equiv)
    }

  -- Pointwise _≡_ is equivalent to _≡_.

  Pointwise-≡ : ∀ {n} {xs ys : Vec A n} →
                Pointwise _≡_ xs ys ⇔ xs ≡ ys
  Pointwise-≡ =
    Equiv.equivalent
      (to ∘ _⟨$⟩_ (Equivalent.to equivalent))
      (λ xs≡ys → P.subst (Pointwise _≡_ _) xs≡ys (refl P.refl))
    where
    to : ∀ {n} {xs ys : Vec A n} → Pointwise′ _≡_ xs ys → xs ≡ ys
    to []               = P.refl
    to (P.refl ∷ xs∼ys) = P.cong (_∷_ _) $ to xs∼ys

  -- Pointwise and Plus commute when the underlying relation is
  -- reflexive.

  ⁺∙⇒∙⁺ : ∀ {_∼_ : Rel A a} {n} {xs ys : Vec A n} →
          Plus (Pointwise _∼_) xs ys → Pointwise (Plus _∼_) xs ys
  ⁺∙⇒∙⁺ [ ρ≈ρ′ ]             = ext (λ x → [ Pointwise.app ρ≈ρ′ x ])
  ⁺∙⇒∙⁺ (ρ ∼⁺⟨ ρ≈ρ′ ⟩ ρ′≈ρ″) =
    ext (λ x → _ ∼⁺⟨ Pointwise.app (⁺∙⇒∙⁺ ρ≈ρ′ ) x ⟩
                     Pointwise.app (⁺∙⇒∙⁺ ρ′≈ρ″) x)

  ∙⁺⇒⁺∙ : ∀ {_∼_ : Rel A a} {n} {xs ys : Vec A n} →
          Reflexive _∼_ →
          Pointwise (Plus _∼_) xs ys → Plus (Pointwise _∼_) xs ys
  ∙⁺⇒⁺∙ {_∼_} x∼x =
    Plus.map (_⟨$⟩_ (Equivalent.from equivalent)) ∘
    helper ∘
    _⟨$⟩_ (Equivalent.to equivalent)
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
      xs∼xs = Equivalent.to equivalent ⟨$⟩ refl x∼x

open Dummy public

-- Note that ∙⁺⇒⁺∙ cannot be defined if the requirement of reflexivity
-- is dropped.

private

 module Counterexample where

  data D : Set where
    i j x y z : D

  data _R_ : Rel D zero where
    iRj : i R j
    xRy : x R y
    yRz : y R z

  xR⁺z : x [ _R_ ]⁺ z
  xR⁺z =
    x  ∼⁺⟨ [ xRy ] ⟩
    y  ∼⁺⟨ [ yRz ] ⟩∎
    z  ∎

  ix = i ∷ x ∷ []
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
    ¬ix⁺∙jz (Equivalent.to Plus.equivalent ⟨$⟩
               Plus.map (_⟨$⟩_ (Equivalent.to equivalent))
                 (∙⁺⇒⁺∙ (Equivalent.from equivalent ⟨$⟩ ix∙⁺jz)))

-- Map.

map : ∀ {a} {A : Set a} {_R_ _R′_ : Rel A a} {n} →
      _R_ ⇒ _R′_ → Pointwise _R_ ⇒ Pointwise _R′_ {n}
map R⇒R′ xsRys = ext λ i →
  R⇒R′ (Pointwise.app xsRys i)

-- A variant.

gmap : ∀ {a} {A A′ : Set a}
         {_R_ : Rel A a} {_R′_ : Rel A′ a} {f : A → A′} {n} →
       _R_ =[ f ]⇒ _R′_ →
       Pointwise _R_ =[ Vec.map {n = n} f ]⇒ Pointwise _R′_
gmap {_R′_ = _R′_} {f} R⇒R′ {i = xs} {j = ys} xsRys = ext λ i →
  let module M = Morphism (VecProp.lookup-morphism i) in
  P.subst₂ _R′_ (P.sym $ M.op-<$> f xs)
                (P.sym $ M.op-<$> f ys)
                (R⇒R′ (Pointwise.app xsRys i))
