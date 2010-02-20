------------------------------------------------------------------------
-- Properties related to list membership
------------------------------------------------------------------------

-- List membership is defined in Data.List.Any. This module does not
-- treat the general variant of list membership, parametrised on a
-- setoid, only the variant where the equality is fixed to be
-- propositional equality.

module Data.List.Any.Membership where

open import Algebra
open import Category.Monad
open import Data.Bool
open import Data.Empty
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
import Function.Injection as Inj
open import Function.Inverse as Inv using (_⇿_; module Inverse)
open import Function.Inverse.TypeIsomorphisms
open import Data.List as List
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Properties
open import Data.Nat as Nat
import Data.Nat.Properties as NatProp
open import Data.Product as Prod
open import Data.Sum as Sum
open import Level
open import Relation.Binary
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; _≗_)
import Relation.Binary.Props.DecTotalOrder as DTOProps
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Unary using (_⟨×⟩_)
open import Relation.Nullary
open import Relation.Nullary.Negation

open Any.Membership-≡
open RawMonad List.monad
private
  module ×⊎ {ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring ℓ)
  module BagS {A : Set} = Setoid (Any.Membership-≡.Bag-equality {A})

------------------------------------------------------------------------
-- Properties relating _∈_ to various list functions

map-∈⇿ : ∀ {A B : Set} {f : A → B} {y xs} →
         (∃ λ x → x ∈ xs × y ≡ f x) ⇿ y ∈ List.map f xs
map-∈⇿ {f = f} {y} {xs} = begin
  (∃ λ x → x ∈ xs × y ≡ f x)  ⇿⟨ Any⇿ ⟩
  Any (λ x → y ≡ f x) xs      ⇿⟨ map⇿ ⟩
  y ∈ List.map f xs           ∎
  where open Inv.⇿-Reasoning

concat-∈⇿ : ∀ {A : Set} {x : A} {xss} →
            (∃ λ xs → x ∈ xs × xs ∈ xss) ⇿ x ∈ concat xss
concat-∈⇿ {x = x} {xss} = begin
  (∃ λ xs → x ∈ xs × xs ∈ xss)  ⇿⟨ Σ.⇿ $ ×⊎.*-comm _ _ ⟩
  (∃ λ xs → xs ∈ xss × x ∈ xs)  ⇿⟨ Any⇿ ⟩
  Any (Any (_≡_ x)) xss         ⇿⟨ concat⇿ ⟩
  x ∈ concat xss                ∎
  where open Inv.⇿-Reasoning

>>=-∈⇿ : ∀ {A B : Set} {xs} {f : A → List B} {y} →
         (∃ λ x → x ∈ xs × y ∈ f x) ⇿ y ∈ (xs >>= f)
>>=-∈⇿ {xs = xs} {f} {y} = begin
  (∃ λ x → x ∈ xs × y ∈ f x)  ⇿⟨ Any⇿ ⟩
  Any (Any (_≡_ y) ∘ f) xs    ⇿⟨ >>=⇿ ⟩
  y ∈ (xs >>= f)              ∎
  where open Inv.⇿-Reasoning

⊛-∈⇿ : ∀ {A B : Set} (fs : List (A → B)) {xs y} →
       (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x) ⇿ y ∈ fs ⊛ xs
⊛-∈⇿ fs {xs} {y} = begin
  (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x)       ⇿⟨ Σ.⇿ ∃∃⇿∃∃ ⟩
  (∃ λ f → f ∈ fs × ∃ λ x → x ∈ xs × y ≡ f x)  ⇿⟨ Σ.⇿ (Inv.id ×-⇿ Any⇿) ⟩
  (∃ λ f → f ∈ fs × Any (_≡_ y ∘ f) xs)        ⇿⟨ Any⇿ ⟩
  Any (λ f → Any (_≡_ y ∘ f) xs) fs            ⇿⟨ ⊛⇿ ⟩
  y ∈ fs ⊛ xs                                  ∎
  where open Inv.⇿-Reasoning

⊗-∈⇿ : ∀ {A B : Set} {xs ys} {x : A} {y : B} →
       (x ∈ xs × y ∈ ys) ⇿ (x , y) ∈ (xs ⊗ ys)
⊗-∈⇿ {A} {B} {xs} {ys} {x} {y} = begin
  (x ∈ xs × y ∈ ys)                ⇿⟨ ⊗⇿′ ⟩
  Any (_≡_ x ⟨×⟩ _≡_ y) (xs ⊗ ys)  ⇿⟨ Any-cong helper BagS.refl ⟩
  (x , y) ∈ (xs ⊗ ys)              ∎
  where
  open Inv.⇿-Reasoning

  helper : (p : A × B) → (x ≡ proj₁ p × y ≡ proj₂ p) ⇿ (x , y) ≡ p
  helper (x′ , y′) = record
    { to         = P.→-to-⟶ (uncurry $ P.cong₂ _,_)
    ; from       = P.→-to-⟶ < P.cong proj₁ , P.cong proj₂ >
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.cong₂ _,_ (P.proof-irrelevance _ _)
                                             (P.proof-irrelevance _ _)
      ; right-inverse-of = λ _ → P.proof-irrelevance _ _
      }
    }

------------------------------------------------------------------------
-- Various functions are monotone

mono : ∀ {A : Set} {P : A → Set} {xs ys} →
       xs ⊆ ys → Any P xs → Any P ys
mono xs⊆ys =
  _⟨$⟩_ (Inverse.to Any⇿) ∘
  Prod.map id (Prod.map xs⊆ys id) ∘
  _⟨$⟩_ (Inverse.from Any⇿)

map-mono : ∀ {A B : Set} (f : A → B) {xs ys} →
           xs ⊆ ys → List.map f xs ⊆ List.map f ys
map-mono f xs⊆ys =
  _⟨$⟩_ (Inverse.to map-∈⇿) ∘
  Prod.map id (Prod.map xs⊆ys id) ∘
  _⟨$⟩_ (Inverse.from map-∈⇿)

_++-mono_ : ∀ {A : Set} {xs₁ xs₂ ys₁ ys₂ : List A} →
            xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → xs₁ ++ xs₂ ⊆ ys₁ ++ ys₂
_++-mono_ xs₁⊆ys₁ xs₂⊆ys₂ =
  _⟨$⟩_ (Inverse.to ++⇿) ∘
  Sum.map xs₁⊆ys₁ xs₂⊆ys₂ ∘
  _⟨$⟩_ (Inverse.from ++⇿)

concat-mono : ∀ {A : Set} {xss yss : List (List A)} →
              xss ⊆ yss → concat xss ⊆ concat yss
concat-mono xss⊆yss =
  _⟨$⟩_ (Inverse.to concat-∈⇿) ∘
  Prod.map id (Prod.map id xss⊆yss) ∘
  _⟨$⟩_ (Inverse.from concat-∈⇿)

>>=-mono : ∀ {A B : Set} (f g : A → List B) {xs ys} →
           xs ⊆ ys → (∀ {x} → f x ⊆ g x) →
           (xs >>= f) ⊆ (ys >>= g)
>>=-mono f g xs⊆ys f⊆g =
  _⟨$⟩_ (Inverse.to >>=-∈⇿) ∘
  Prod.map id (Prod.map xs⊆ys f⊆g) ∘
  _⟨$⟩_ (Inverse.from >>=-∈⇿)

_⊛-mono_ : ∀ {A B : Set} {fs gs : List (A → B)} {xs ys} →
           fs ⊆ gs → xs ⊆ ys → (fs ⊛ xs) ⊆ (gs ⊛ ys)
_⊛-mono_ {fs = fs} {gs} fs⊆gs xs⊆ys =
  _⟨$⟩_ (Inverse.to $ ⊛-∈⇿ gs) ∘
  Prod.map id (Prod.map id (Prod.map fs⊆gs (Prod.map xs⊆ys id))) ∘
  _⟨$⟩_ (Inverse.from $ ⊛-∈⇿ fs)

_⊗-mono_ : {A B : Set} {xs₁ ys₁ : List A} {xs₂ ys₂ : List B} →
           xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → (xs₁ ⊗ xs₂) ⊆ (ys₁ ⊗ ys₂)
xs₁⊆ys₁ ⊗-mono xs₂⊆ys₂ =
  _⟨$⟩_ (Inverse.to ⊗-∈⇿) ∘
  Prod.map xs₁⊆ys₁ xs₂⊆ys₂ ∘
  _⟨$⟩_ (Inverse.from ⊗-∈⇿)

any-mono : ∀ {A : Set} (p : A → Bool) →
           ∀ {xs ys} → xs ⊆ ys → T (any p xs) → T (any p ys)
any-mono p xs⊆ys =
  _⟨$⟩_ (Equivalent.to any⇔) ∘
  mono xs⊆ys ∘
  _⟨$⟩_ (Equivalent.from any⇔)

map-with-∈-mono :
  {A B : Set} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
              {ys : List A} {g : ∀ {x} → x ∈ ys → B}
  (xs⊆ys : xs ⊆ ys) → (∀ {x} → f {x} ≗ g ∘ xs⊆ys) →
  map-with-∈ xs f ⊆ map-with-∈ ys g
map-with-∈-mono {f = f} {g = g} xs⊆ys f≈g {x} =
  _⟨$⟩_ (Inverse.to map-with-∈⇿) ∘
  Prod.map id (Prod.map xs⊆ys (λ {x∈xs} x≡fx∈xs → begin
    x               ≡⟨ x≡fx∈xs ⟩
    f x∈xs          ≡⟨ f≈g x∈xs ⟩
    g (xs⊆ys x∈xs)  ∎)) ∘
  _⟨$⟩_ (Inverse.from map-with-∈⇿)
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- Other properties

-- Only a finite number of distinct elements can be members of a
-- given list.

finite : {A : Set} (f : Inj.Injection (P.setoid ℕ) (P.setoid A)) →
         ∀ xs → ¬ (∀ i → Inj.Injection.to f ⟨$⟩ i ∈ xs)
finite     inj []       ∈[]   with ∈[] zero
... | ()
finite {A} inj (x ∷ xs) ∈x∷xs = excluded-middle helper
  where
  open Inj.Injection inj

  module DTO = DecTotalOrder Nat.decTotalOrder
  module STO = StrictTotalOrder
                 (DTOProps.strictTotalOrder Nat.decTotalOrder)
  module CS  = CommutativeSemiring NatProp.commutativeSemiring

  not-x : ∀ {i} → ¬ (to ⟨$⟩ i ≡ x) → to ⟨$⟩ i ∈ xs
  not-x {i} ≢x with ∈x∷xs i
  ... | here  ≡x  = ⊥-elim (≢x ≡x)
  ... | there ∈xs = ∈xs

  helper : ¬ Dec (∃ λ i → to ⟨$⟩ i ≡ x)
  helper (no ≢x)        = finite inj  xs (λ i → not-x (≢x ∘ _,_ i))
  helper (yes (i , ≡x)) = finite inj′ xs ∈xs
    where
    open P

    f : ℕ → A
    f j with STO.compare i j
    f j | tri< _ _ _ = to ⟨$⟩ suc j
    f j | tri≈ _ _ _ = to ⟨$⟩ suc j
    f j | tri> _ _ _ = to ⟨$⟩ j

    ∈-if-not-i : ∀ {j} → i ≢ j → to ⟨$⟩ j ∈ xs
    ∈-if-not-i i≢j = not-x (i≢j ∘ injective ∘ trans ≡x ∘ sym)

    lemma : ∀ {k j} → k ≤ j → suc j ≢ k
    lemma 1+j≤j refl = NatProp.1+n≰n 1+j≤j

    ∈xs : ∀ j → f j ∈ xs
    ∈xs j with STO.compare i j
    ∈xs j  | tri< (i≤j , _) _ _ = ∈-if-not-i (lemma i≤j ∘ sym)
    ∈xs j  | tri> _ i≢j _       = ∈-if-not-i i≢j
    ∈xs .i | tri≈ _ refl _      =
      ∈-if-not-i (NatProp.m≢1+m+n i ∘
                  subst (_≡_ i ∘ suc) (sym $ proj₂ CS.+-identity i))

    injective′ : Inj.Injective {B = P.setoid A} (→-to-⟶ f)
    injective′ {j} {k} eq with STO.compare i j | STO.compare i k
    ... | tri< _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
    ... | tri< _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
    ... | tri< (i≤j , _) _ _ | tri> _ _ (k≤i , _) = ⊥-elim (lemma (DTO.trans k≤i i≤j)           $ injective eq)
    ... | tri≈ _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
    ... | tri≈ _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
    ... | tri≈ _ i≡j _       | tri> _ _ (k≤i , _) = ⊥-elim (lemma (subst (_≤_ k) i≡j k≤i)       $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri< (i≤k , _) _ _ = ⊥-elim (lemma (DTO.trans j≤i i≤k)     $ sym $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri≈ _ i≡k _       = ⊥-elim (lemma (subst (_≤_ j) i≡k j≤i) $ sym $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri> _ _ (k≤i , _) =                                               injective eq

    inj′ = record { to = →-to-⟶ f; injective = injective′ }
