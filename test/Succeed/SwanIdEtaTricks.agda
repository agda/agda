{-# OPTIONS --cubical #-}

module SwanIdEtaTricks where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)
import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Id renaming (IdJ to J ; primIdElim to idElim ; reflId to refl ; Id to infix 4 _≡_)
open import Agda.Builtin.Cubical.Sub renaming (primSubOut to outS; Sub to _[_↦_])

{-# NO_UNIVERSE_CHECK #-}
record Smuggle {ℓ} (A : SSet ℓ) : Type ℓ where
  constructor shh
  field huh! : A

data IdView {ℓ} {A : Type ℓ} {x : A} : {y : A} → x ≡ y → SSet ℓ where
  ⟨_,_,_⟩
    : (φ : I) (z : A [ φ ↦ (λ ._ → x) ]) (p : (PathP (λ _ → A) x (outS z)) [ φ ↦ (λ { (φ = i1) → λ i → x } ) ])
    → IdView (conid φ (outS p))

_ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ primExpandId p
_ = λ p → refl

-- conveniently evil:
view : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → IdView p
view p = Smuggle.huh! (idElim (λ y p → Smuggle (IdView p)) (λ φ y w → shh ⟨ φ , y , w ⟩) (primExpandId p))
--                                                       new primitive powers this stuff: ^^^^^^^^^^^^^^
-- the code below could be rewritten not to use view/Smuggle at all (by
-- inlining the primIdElim (primExpandId p) calls), which would make it
-- compatible with --safe, but noisier. i went with the short & even
-- more evil version

_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} {y} {z} p q with view p | view q
... | ⟨ φ , y′ , p ⟩ | ⟨ ψ , z′ , q ⟩ = conid (φ ∧ ψ) λ i → hcomp
  (λ { j (i = i0) → x
     ; j (i = i1) → outS q j
     ; j (φ = i1) → outS q (i ∧ j)
     ; j (ψ = i1) → outS p i
     })
  (outS p i)

idl : {A : Type} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
idl p = refl

idr : {A : Type} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
idr p = refl

assoc′
  : {A : Type} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → (p ∙ (q ∙ r)) ≡ ((p ∙ q) ∙ r)
assoc′ refl q r = refl

ap : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f {x} p with view p
... | ⟨ φ , y′ , w ⟩ = conid φ λ i → f (outS w i)

sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p with view p
... | ⟨ φ , y′ , w ⟩ = conid φ λ i → outS w (~ i)

sym-inv : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym-inv p = refl

J-comp : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} {P : ∀ y → x ≡ y → Set ℓ'} →
         (d : P x (conid i1 (λ i → x))) → J P d (conid i1 (λ i → x)) ≡ d
J-comp d = refl

ap-comp
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ′′} {x y : A} (p : x ≡ y)
  → (f : B → C) (g : A → B)
  → ap f (ap g p) ≡ ap (λ x → f (g x)) p
ap-comp p f g = refl

ap-comp-path
  : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} {x y z : A} (p : x ≡ y) (q : y ≡ z) (f : A → B)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-comp-path refl q f = refl

pathToId : ∀ {ℓ} {A : Type ℓ} {x y : A} → PathP (λ _ → A) x y → x ≡ y
pathToId {x = x} p = transp (λ i → x ≡ p i) i0 refl
