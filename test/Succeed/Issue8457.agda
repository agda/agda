{-# OPTIONS --without-K #-}

module Issue8457 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality as ≡ hiding (refl)

------------------------------------- Preamble: extracted from Standard Library  -------------------------------------

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

      reflexive : ∀ {x y} → x ≡ y → x ≈ y
      reflexive ≡.refl = refl

  module RelationBinaryBundles where
    open RelationBinaryStructures

    record Setoid : Set₁ where
      infix 4 _≈_
      field
        Carrier       : Set
        _≈_           : Carrier → Carrier → Set
        isEquivalence : IsEquivalence _≈_

      open IsEquivalence isEquivalence public
        using (refl; reflexive)

  module FunctionDefinitions where
    private variable A B : Set

    module _
      (_≈₁_ : A → A → Set) -- Equality over the domain
      (_≈₂_ : B → B → Set) -- Equality over the codomain
      where

      Congruent : (A → B) → Set _
      Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

      Inverseˡ : (A → B) → (B → A) → Set _
      Inverseˡ f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

      Inverseʳ : (A → B) → (B → A) → Set _
      Inverseʳ f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

      Inverseᵇ : (A → B) → (B → A) → Set _
      Inverseᵇ f g = Σ (Inverseˡ f g) λ _ → Inverseʳ f g

    StrictlyInverseˡ : (B → B → Set) → (A → B) → (B → A) → Set _
    StrictlyInverseˡ _≈₂_ f g = ∀ y → f (g y) ≈₂ y

    StrictlyInverseʳ : (A → A → Set) → (A → B) → (B → A) → Set _
    StrictlyInverseʳ _≈₁_ f g = ∀ x → g (f x) ≈₁ x

  module _ where
    open RelationBinaryBundles
    open RelationBinaryStructures

    module FunctionStructures
      {A : Set} (_≈₁_ : A → A → Set) -- Equality over the domain
      {B : Set} (_≈₂_ : B → B → Set) -- Equality over the codomain
      where

      open FunctionDefinitions

      ------------------------------------------------------------------------
      -- One element structures
      ------------------------------------------------------------------------

      record IsCongruent (to : A → B) : Set where
        field
          cong           : Congruent _≈₁_ _≈₂_ to
          isEquivalence₁ : IsEquivalence _≈₁_
          isEquivalence₂ : IsEquivalence _≈₂_

        module Eq₁ where

          setoid : Setoid {-lzero lzero-}
          setoid = record
            { isEquivalence = isEquivalence₁
            }

          open Setoid setoid public

        module Eq₂ where

          setoid : Setoid {-lzero lzero-}
          setoid = record
            { isEquivalence = isEquivalence₂
            }

          open Setoid setoid public

      ------------------------------------------------------------------------
      -- Two element structures
      ------------------------------------------------------------------------

      record IsLeftInverse (to : A → B) (from : B → A) : Set where
        field
          isCongruent  : IsCongruent to
          from-cong    : Congruent _≈₂_ _≈₁_ from
          inverseˡ     : Inverseˡ _≈₁_ _≈₂_ to from

        open IsCongruent isCongruent public
          renaming (cong to to-cong)

        strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
        strictlyInverseˡ x = inverseˡ Eq₁.refl

      record IsRightInverse (to : A → B) (from : B → A) : Set where
        field
          isCongruent : IsCongruent to
          from-cong   : Congruent _≈₂_ _≈₁_ from
          inverseʳ    : Inverseʳ _≈₁_ _≈₂_ to from

        open IsCongruent isCongruent public
          renaming (cong to to-cong)

        strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from
        strictlyInverseʳ x = inverseʳ Eq₂.refl

      record IsInverse (to : A → B) (from : B → A) : Set where
        field
          isLeftInverse : IsLeftInverse to from
          inverseʳ      : Inverseʳ _≈₁_ _≈₂_ to from

        open IsLeftInverse isLeftInverse public

        isRightInverse : IsRightInverse to from
        isRightInverse = record
          { isCongruent = isCongruent
          ; from-cong   = from-cong
          ; inverseʳ    = inverseʳ
          }

        open IsRightInverse isRightInverse public
          using (strictlyInverseʳ)

        inverse : Inverseᵇ _≈₁_ _≈₂_ to from
        inverse = inverseˡ , inverseʳ

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
    open FunctionDefinitions
    open RelationBinaryBundles
    open Setoid using (isEquivalence)

    ------------------------------------------------------------------------
    -- Setoid bundles
    ------------------------------------------------------------------------

    module _ (From : Setoid) (To : Setoid) where

      open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
      open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
      open FunctionStructures _≈₁_ _≈₂_

      record LeftInverse : Set where
        field
          to        : A → B
          from      : B → A
          to-cong   : Congruent _≈₁_ _≈₂_ to
          from-cong : Congruent _≈₂_ _≈₁_ from
          inverseˡ  : Inverseˡ _≈₁_ _≈₂_ to from

        isCongruent : IsCongruent to
        isCongruent = record
          { cong           = to-cong
          ; isEquivalence₁ = isEquivalence From
          ; isEquivalence₂ = isEquivalence To
          }

        isLeftInverse : IsLeftInverse to from
        isLeftInverse = record
          { isCongruent = isCongruent
          ; from-cong   = from-cong
          ; inverseˡ    = inverseˡ
          }

        open IsLeftInverse isLeftInverse public
          using (module Eq₁; module Eq₂; strictlyInverseˡ)

      record RightInverse : Set where
        field
          to        : A → B
          from      : B → A
          to-cong   : Congruent _≈₁_ _≈₂_ to
          from-cong : ∀ {x y} → x ≈₂ y → from x ≈₁ from y
          inverseʳ  : Inverseʳ _≈₁_ _≈₂_ to from

        isCongruent : IsCongruent to
        isCongruent = record
          { cong           = to-cong
          ; isEquivalence₁ = isEquivalence From
          ; isEquivalence₂ = isEquivalence To
          }

        isRightInverse : IsRightInverse to from
        isRightInverse = record
          { isCongruent = isCongruent
          ; from-cong   = from-cong
          ; inverseʳ    = inverseʳ
          }

        open IsRightInverse isRightInverse public
          using (module Eq₁; module Eq₂; strictlyInverseʳ)

      record Inverse : Set where
        field
          to        : A → B
          from      : B → A
          to-cong   : Congruent _≈₁_ _≈₂_ to
          from-cong : Congruent _≈₂_ _≈₁_ from
          inverse   : Inverseᵇ _≈₁_ _≈₂_ to from

        inverseˡ : Inverseˡ _≈₁_ _≈₂_ to from
        inverseˡ = proj₁ inverse

        inverseʳ : Inverseʳ _≈₁_ _≈₂_ to from
        inverseʳ = proj₂ inverse

        leftInverse : LeftInverse
        leftInverse = record
          { to-cong   = to-cong
          ; from-cong = from-cong
          ; inverseˡ  = inverseˡ
          }

        rightInverse : RightInverse
        rightInverse = record
          { to-cong   = to-cong
          ; from-cong = from-cong
          ; inverseʳ  = inverseʳ
          }

        open LeftInverse leftInverse   public using (isLeftInverse; strictlyInverseˡ)
        open RightInverse rightInverse public using (isRightInverse; strictlyInverseʳ)

        isInverse : IsInverse to from
        isInverse = record
          { isLeftInverse = isLeftInverse
          ; inverseʳ      = inverseʳ
          }

        open IsInverse isInverse public using (module Eq₁; module Eq₂)

    _↔_ : Set → Set → Set _
    A ↔ B = Inverse (RelationBinaryPropositionalEqualityProperties.setoid A) (RelationBinaryPropositionalEqualityProperties.setoid B)

    module _ {A : Set} {B : Set} where
      mk↔ : ∀ {to : A → B} {from : B → A} → Inverseᵇ _≡_ _≡_ to from → A ↔ B
      mk↔ {to} {from} inv = record
        { to        = to
        ; from      = from
        ; to-cong   = cong1 to
        ; from-cong = cong1 from
        ; inverse   = inv
        }

      mk↔ₛ′ : ∀ (to : A → B) (from : B → A) →
              StrictlyInverseˡ _≡_ to from →
              StrictlyInverseʳ _≡_ to from →
              A ↔ B
      mk↔ₛ′ to from invˡ invʳ = mk↔ {to} {from}
        ( (λ y≡from → trans1 (cong1 to y≡from) (invˡ _))
        , λ y≡to → trans1 (cong1 from y≡to) (invʳ _)
        )

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
