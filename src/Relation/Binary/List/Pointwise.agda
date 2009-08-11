------------------------------------------------------------------------
-- Pointwise relation on lists
------------------------------------------------------------------------

module Relation.Binary.List.Pointwise where

open import Data.Function
open import Data.Product
open import Data.List
open import Relation.Nullary
open import Relation.Binary

private
 module Dummy {a : Set} where

  infixr 5 _∷_

  data List-Rel (_∼_ : Rel a) : List a → List a → Set where
    []  : List-Rel _∼_ [] []
    _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : List-Rel _∼_ xs ys) →
          List-Rel _∼_ (x ∷ xs) (y ∷ ys) 

  List-head : ∀ {_∼_}{x y : a}{xs ys} → List-Rel _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  List-head (x∼y ∷ xs∼ys) = x∼y

  List-tail : ∀ {_∼_}{x y : a}{xs ys} → List-Rel _∼_ (x ∷ xs) (y ∷ ys) → List-Rel _∼_ xs ys
  List-tail (x∼y ∷ xs∼ys) = xs∼ys

  List-reflexive : ∀ {≈ ∼} → ≈ ⇒ ∼ → (List-Rel ≈) ⇒ (List-Rel ∼)
  List-reflexive ≈⇒∼ [] = []
  List-reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ List-reflexive ≈⇒∼ xs≈ys

  List-refl : ∀ {∼} → Reflexive ∼ → Reflexive (List-Rel ∼)
  List-refl refl {[]} = []
  List-refl refl {x ∷ xs} = refl ∷ List-refl refl

  List-symmetric : ∀ {∼} → Symmetric ∼ → Symmetric (List-Rel ∼)
  List-symmetric sym [] = []
  List-symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ List-symmetric sym xs∼ys
  
  List-transitive : ∀ {∼} → Transitive ∼ → Transitive (List-Rel ∼)
  List-transitive trans [] [] = []
  List-transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) = 
       trans x∼y y∼z ∷ List-transitive trans xs∼ys ys∼zs
 
  List-antisymmetric : ∀ {≈ ≤} → Antisymmetric ≈ ≤ →
                       Antisymmetric (List-Rel ≈) (List-Rel ≤)
  List-antisymmetric antisym [] [] = []
  List-antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) = 
       antisym x∼y y∼x ∷ List-antisymmetric antisym xs∼ys ys∼xs

  List-≈-respects₂ : ∀ {≈ ∼} → ∼ Respects₂ ≈ → (List-Rel ∼) Respects₂ (List-Rel ≈)
  List-≈-respects₂ {≈} {∼} resp = (λ {xs} {ys} {zs} → resp¹ {xs} {ys} {zs}) ,
                                    λ {xs} {ys} {zs} → resp² {xs} {ys} {zs} 
   where
    resp¹ : ∀ {xs} → (List-Rel ∼ xs) Respects (List-Rel ≈)
    resp¹ [] [] = []
    resp¹ (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) = proj₁ resp x≈y z∼x ∷ resp¹ xs≈ys zs∼xs

    resp² : ∀ {ys} → (flip₁ (List-Rel ∼) ys) Respects (List-Rel ≈)
    resp² [] [] = []
    resp² (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) = proj₂ resp x≈y x∼z ∷ resp² xs≈ys xs∼zs

  List-decidable : ∀ {∼} → Decidable ∼ → Decidable (List-Rel ∼)
  List-decidable dec [] [] = yes []
  List-decidable dec [] (y ∷ ys) = no (λ ())
  List-decidable dec (x ∷ xs) [] = no (λ ())
  List-decidable dec (x ∷ xs) (y ∷ ys) with dec x y
  ... | no ¬x∼y = no (λ p → ¬x∼y (List-head p))
  ... | yes x∼y with List-decidable dec xs ys
  ...           | no ¬xs∼ys = no (λ p → ¬xs∼ys (List-tail p))
  ...           | yes xs∼ys = yes (x∼y ∷ xs∼ys)

  List-isEquivalence : ∀ {≈} → IsEquivalence ≈ → IsEquivalence (List-Rel ≈)
  List-isEquivalence eq = record
    { refl = λ {xs} → List-refl (refl eq) {xs}
    ; sym = λ {xs} {ys} → List-symmetric (sym eq) {xs} {ys}
    ; trans = λ {xs} {ys} {zs} → List-transitive (trans eq) {xs} {ys} {zs}
    }
    where open IsEquivalence

  List-isPreorder : ∀ {≈ ∼} → IsPreorder ≈ ∼ → IsPreorder (List-Rel ≈) (List-Rel ∼)
  List-isPreorder pre = record
    { isEquivalence = List-isEquivalence (isEquivalence pre)
    ; reflexive = λ {xs} {ys} → List-reflexive (reflexive pre)
    ; trans = λ {xs} {ys} {zs} → List-transitive (trans pre)
    ; ∼-resp-≈ = List-≈-respects₂ (∼-resp-≈ pre)
    }
    where open IsPreorder

  List-isDecEquivalence : ∀ {≈} → IsDecEquivalence ≈ → IsDecEquivalence (List-Rel ≈)
  List-isDecEquivalence eq = record
    { isEquivalence = List-isEquivalence (isEquivalence eq)
    ; _≟_ = List-decidable (_≟_ eq)
    }
    where open IsDecEquivalence

  List-isPartialOrder : ∀ {≈ ≤} → IsPartialOrder ≈ ≤ → IsPartialOrder (List-Rel ≈) (List-Rel ≤)
  List-isPartialOrder po = record
    { isPreorder = List-isPreorder (isPreorder po)
    ; antisym = λ {xs} {ys} → List-antisymmetric (antisym po)
    } where open IsPartialOrder

open Dummy public

List-preorder : Preorder → Preorder
List-preorder p = record
  { isPreorder = List-isPreorder (isPreorder p)
  } where open Preorder

List-setoid : Setoid → Setoid
List-setoid s = record
  { isEquivalence = List-isEquivalence (isEquivalence s)
  } where open Setoid

List-decSetoid : DecSetoid → DecSetoid
List-decSetoid s = record
  { isDecEquivalence = List-isDecEquivalence (isDecEquivalence s)
  } where open DecSetoid

List-poset : Poset → Poset
List-poset s = record
  { isPartialOrder = List-isPartialOrder (isPartialOrder s)
  } where open Poset