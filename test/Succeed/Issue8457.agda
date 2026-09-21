{-# OPTIONS --without-K #-}

module Issue8457 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality as ≡ hiding (refl)

---------------- Preamble: extracted and simplified from Standard Library ----------------

record ⊤ : Set where constructor tt

trans1 : {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans1 ≡.refl ≡.refl = ≡.refl

cong1 :  {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong1 f ≡.refl = ≡.refl

cong2 :  {X Y Z : Set} {a c : X} {b d : Y} → (f : X → Y → Z) → a ≡ c → b ≡ d → f a b ≡ f c d
cong2 f ≡.refl ≡.refl = ≡.refl

map2 : {A B : Set} {C : A → Set} {D : B → Set} → (f : A → B) → (∀ {x} → C x → D (f x)) → Σ A C → Σ B D
map2 f g (x , y) = f x , g y

module StdLib where
  module RelationBinaryStructures {A : Set} (_≈_ : A → A → Set) where
    record IsEquivalence : Set where
      field
        refl  : ∀ {x} →  x ≈ x
        sym   : ∀ {x y} → x ≈ y → y ≈ x
        trans : ∀ {i j k} → i ≈ j → j ≈ k → i ≈ k

  module RelationBinaryBundles where
    open RelationBinaryStructures

    record Setoid : Set₁ where
      infix 4 _≈_
      field
        Carrier       : Set
        _≈_           : Carrier → Carrier → Set
        isEquivalence : IsEquivalence _≈_

      open IsEquivalence isEquivalence public
        using (refl)

  module RelationBinaryPropositionalEqualityProperties where
    open RelationBinaryBundles
    open RelationBinaryStructures

    isEquivalence : {A : Set} → IsEquivalence {A = A} _≡_
    isEquivalence = record
      { refl  = ≡.refl
      ; sym   = λ where ≡.refl → ≡.refl
      ; trans = trans1
      }

    setoid : Set → Setoid
    setoid A = record
      { Carrier       = A
      ; _≈_           = _≡_
      ; isEquivalence = isEquivalence
      }

  module FunctionBundles where
    open RelationBinaryBundles

    ------------------------------------------------------------------------
    -- Setoid bundles
    ------------------------------------------------------------------------

    module _ (From : Setoid) (To : Setoid) where
      open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
      open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
      open RelationBinaryStructures

      record Inverse : Set where
        field
          to        : A → B
          from      : B → A
          strictlyInverseˡ : ∀ y → to (from y) ≈₂ y
          strictlyInverseʳ : ∀ x → from (to x) ≈₁ x

    _↔_ : Set → Set → Set _
    A ↔ B = Inverse (RelationBinaryPropositionalEqualityProperties.setoid A) (RelationBinaryPropositionalEqualityProperties.setoid B)

    mk↔ₛ′ : {A B : Set} (to : A → B) (from : B → A) →
            (∀ y → to (from y) ≡ y) →
            (∀ x → from (to x) ≡ x) →
            A ↔ B
    mk↔ₛ′ to from invˡ invʳ = record
      { to = to
      ; from = from
      ; strictlyInverseˡ = invˡ
      ; strictlyInverseʳ = invʳ
      }

------------------------------------- Main: extracted from BiSikkel.MSTT.Extraction -------------------------------------

open StdLib.FunctionBundles

record Tyᴹ (Γ : Set) : Set₁ where
  field
    ty-cell : Γ → Set
    ty-hom : ∀ {γy γx} → ty-cell γy → ty-cell γx

open Tyᴹ public

postulate
  to-Σ-ty-eq : {Γ : Set} (T : Tyᴹ Γ)
    {a b : Γ} → a ≡ b → {ta : T .ty-cell a} {tb : T  .ty-cell b} →
    T .ty-hom ta ≡ tb →
    (a , ta) ≡ (b , tb)

data Ty : Set where
  atom : Ty

⟦_⟧ty : Ty → {sΓ : Set} → Tyᴹ sΓ
⟦ atom ⟧ty .ty-cell _ = ⊤
⟦ atom ⟧ty .ty-hom a = a

record ExtractableCtx (Γ : Set) : Set₁ where
  field
    AgdaCtx : Set
    extract-ctx-iso : Γ ↔ AgdaCtx
open ExtractableCtx {{...}} public

record ExtractableTy (T : Ty) : Set₁ where
  field
    AgdaTy : Set
    extract-ty-iso : {sΓ : Set} {γ : sΓ} → (⟦ T ⟧ty  .ty-cell γ) ↔ AgdaTy
open ExtractableTy {{...}} public

postulate
  extract-ty-iso-transport : {T : Ty} {{exT : ExtractableTy T}}
    {sΓ : Set} {γ γ' : sΓ} →
    {t : ⟦ T ⟧ty .ty-cell γ} →
    ty-hom ⟦ T ⟧ty {γ'} {γ}
      (Inverse.from (extract-ty-iso {{exT}}) (Inverse.to (extract-ty-iso {{exT}}) t)) ≡ t
instance
  ,,-extractable :
    {Γ : Set} → {{ExtractableCtx Γ}} →
    {T : Ty} → {{ExtractableTy T}} →
    ExtractableCtx (Σ Γ (λ γ → ⟦ T ⟧ty  .ty-cell γ))

  ExtractableCtx.AgdaCtx (,,-extractable {Γ} {T}) = Σ (AgdaCtx {Γ}) λ _ → AgdaTy {T}
  ExtractableCtx.extract-ctx-iso (,,-extractable {Γ} {T}) = mk↔ₛ′
    (map2 (Inverse.to extract-ctx-iso) (Inverse.to extract-ty-iso))
    (map2 (Inverse.from extract-ctx-iso) (Inverse.from extract-ty-iso))
    (λ _ → cong2 _,_ (Inverse.strictlyInverseˡ (extract-ctx-iso {Γ}) _) (Inverse.strictlyInverseˡ extract-ty-iso _))
    (λ _ → to-Σ-ty-eq ⟦ T ⟧ty (Inverse.strictlyInverseʳ extract-ctx-iso _)
      extract-ty-iso-transport)
