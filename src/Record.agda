------------------------------------------------------------------------
-- Record types with manifest fields and "with", based on Randy
-- Pollack's "Dependently Typed Records in Type Theory"
------------------------------------------------------------------------

-- For an example of how this module can be used, see README.Record.

{-# OPTIONS --universe-polymorphism #-}

-- The module is parametrised by the type of labels, which should come
-- with decidable equality.

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Record (Label : Set) (_≟_ : Decidable (_≡_ {A = Label})) where

open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Product hiding (proj₁; proj₂)
open import Data.Unit
open import Function hiding (type-signature)
open import Level
open import Relation.Nullary
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- A Σ-type with a manifest field

-- A variant of Σ where the value of the second field is "manifest"
-- (given by the first).

infix 4 _,

record Manifest-Σ {a b} (A : Set a) {B : A → Set b}
                  (f : (x : A) → B x) : Set a where
  constructor _,
  field proj₁ : A

  proj₂ : B proj₁
  proj₂ = f proj₁

------------------------------------------------------------------------
-- Signatures and records

mutual

  infixl 5 _,_∶_ _,_≔_

  data Signature s : Set (suc s) where
    ∅     : Signature s
    _,_∶_ : (Sig : Signature s)
            (ℓ : Label)
            (A : Record Sig → Set s) →
            Signature s
    _,_≔_ : (Sig : Signature s)
            (ℓ : Label)
            {A : Record Sig → Set s}
            (a : (r : Record Sig) → A r) →
            Signature s

  -- Record is a data type to ensure that the signature can be
  -- inferred from a value of type Record Sig.

  data Record {s} (Sig : Signature s) : Set s where
    rec : (r : Record-fun Sig) → Record Sig

  Record-fun : ∀ {s} → Signature s → Set s
  Record-fun ∅             = Lift ⊤
  Record-fun (Sig , ℓ ∶ A) =          Σ (Record Sig) A
  Record-fun (Sig , ℓ ≔ a) = Manifest-Σ (Record Sig) a

-- A projection function for Record. (Unfortunately Agda as of version
-- 2.2.10 does not allow us to turn Record into a record type.)

rec-fun : ∀ {s} {Sig : Signature s} → Record Sig → Record-fun Sig
rec-fun (rec r) = r

------------------------------------------------------------------------
-- Variants of Signature and Record

-- It may be easier to define values of type Record′ (Sig⇒Sig′ Sig)
-- than of type Record Sig.

mutual

  data Signature′ s : Set (suc s) where
    ∅     : Signature′ s
    _,_∶_ : (Sig : Signature′ s)
            (ℓ : Label)
            (A : Record′ Sig → Set s) →
            Signature′ s
    _,_≔_ : (Sig : Signature′ s)
            (ℓ : Label)
            {A : Record′ Sig → Set s}
            (a : (r : Record′ Sig) → A r) →
            Signature′ s

  Record′ : ∀ {s} → Signature′ s → Set s
  Record′ ∅             = Lift ⊤
  Record′ (Sig , ℓ ∶ A) =          Σ (Record′ Sig) A
  Record′ (Sig , ℓ ≔ a) = Manifest-Σ (Record′ Sig) a

-- We can convert between the two kinds of signatures/records.

mutual

  Sig′⇒Sig : ∀ {s} → Signature′ s → Signature s
  Sig′⇒Sig ∅             = ∅
  Sig′⇒Sig (Sig , ℓ ∶ A) = Sig′⇒Sig Sig , ℓ ∶ (A ∘ Rec⇒Rec′ _)
  Sig′⇒Sig (Sig , ℓ ≔ a) = Sig′⇒Sig Sig , ℓ ≔ (a ∘ Rec⇒Rec′ _)

  Rec⇒Rec′ : ∀ {s} (Sig : Signature′ s) →
             Record (Sig′⇒Sig Sig) → Record′ Sig
  Rec⇒Rec′ ∅             r = rec-fun r
  Rec⇒Rec′ (Sig , ℓ ∶ A) r = (Rec⇒Rec′ _ (Σ.proj₁ r′) , Σ.proj₂ r′)
                                   where r′ = rec-fun r
  Rec⇒Rec′ (Sig , ℓ ≔ a) r = (Rec⇒Rec′ _ (Manifest-Σ.proj₁ r′) ,)
                             where r′ = rec-fun r

mutual

  Sig⇒Sig′ : ∀ {s} → Signature s → Signature′ s
  Sig⇒Sig′ ∅             = ∅
  Sig⇒Sig′ (Sig , ℓ ∶ A) = Sig⇒Sig′ Sig , ℓ ∶ (A ∘ Rec′⇒Rec _)
  Sig⇒Sig′ (Sig , ℓ ≔ a) = Sig⇒Sig′ Sig , ℓ ≔ (a ∘ Rec′⇒Rec _)

  Rec′⇒Rec : ∀ {s} (Sig : Signature s) →
             Record′ (Sig⇒Sig′ Sig) → Record Sig
  Rec′⇒Rec ∅             r = rec r
  Rec′⇒Rec (Sig , ℓ ∶ A) r = rec (Rec′⇒Rec _ (Σ.proj₁ r) , Σ.proj₂ r)
  Rec′⇒Rec (Sig , ℓ ≔ a) r = rec (Rec′⇒Rec _ (Manifest-Σ.proj₁ r) ,)

------------------------------------------------------------------------
-- Labels

-- A signature's labels, starting with the last one.

labels : ∀ {s} → Signature s → List Label
labels ∅             = []
labels (Sig , ℓ ∶ A) = ℓ ∷ labels Sig
labels (Sig , ℓ ≔ a) = ℓ ∷ labels Sig

-- Inhabited if the label is part of the signature.

infix 4 _∈_

_∈_ : ∀ {s} → Label → Signature s → Set
ℓ ∈ Sig =
  foldr (λ ℓ′ → if ⌊ ℓ ≟ ℓ′ ⌋ then const ⊤ else id) ⊥ (labels Sig)

------------------------------------------------------------------------
-- Projections

-- Signature restriction and projection. (Restriction means removal of
-- a given field and all subsequent fields.)

Restrict : ∀ {s} (Sig : Signature s) (ℓ : Label) → ℓ ∈ Sig →
           Signature s
Restrict ∅              ℓ ()
Restrict (Sig , ℓ′ ∶ A) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = Sig
... | no  _ = Restrict Sig ℓ ℓ∈
Restrict (Sig , ℓ′ ≔ a) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = Sig
... | no  _ = Restrict Sig ℓ ℓ∈

Restricted : ∀ {s} (Sig : Signature s) (ℓ : Label) → ℓ ∈ Sig → Set s
Restricted Sig ℓ ℓ∈ = Record (Restrict Sig ℓ ℓ∈)

Proj : ∀ {s} (Sig : Signature s) (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} →
       Restricted Sig ℓ ℓ∈ → Set s
Proj ∅              ℓ {}
Proj (Sig , ℓ′ ∶ A) ℓ with ℓ ≟ ℓ′
... | yes _ = A
... | no  _ = Proj Sig ℓ
Proj (_,_≔_ Sig ℓ′ {A = A} a) ℓ with ℓ ≟ ℓ′
... | yes _ = A
... | no  _ = Proj Sig ℓ

-- Record restriction and projection.

infixl 5 _∣_

_∣_ : ∀ {s} {Sig : Signature s} → Record Sig →
      (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} → Restricted Sig ℓ ℓ∈
_∣_ {Sig = ∅}            r ℓ {}
_∣_ {Sig = Sig , ℓ′ ∶ A} r ℓ with ℓ ≟ ℓ′
... | yes _ = Σ.proj₁ (rec-fun r)
... | no  _ = Σ.proj₁ (rec-fun r) ∣ ℓ
_∣_ {Sig = Sig , ℓ′ ≔ a} r ℓ with ℓ ≟ ℓ′
... | yes _ = Manifest-Σ.proj₁ (rec-fun r)
... | no  _ = Manifest-Σ.proj₁ (rec-fun r) ∣ ℓ

infixl 5 _·_

_·_ : ∀ {s} {Sig : Signature s} (r : Record Sig)
      (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} →
      Proj Sig ℓ {ℓ∈} (r ∣ ℓ)
_·_ {Sig = ∅}            r ℓ {}
_·_ {Sig = Sig , ℓ′ ∶ A} r ℓ with ℓ ≟ ℓ′
... | yes _ = Σ.proj₂ (rec-fun r)
... | no  _ = Σ.proj₁ (rec-fun r) · ℓ
_·_ {Sig = Sig , ℓ′ ≔ a} r ℓ with ℓ ≟ ℓ′
... | yes _ = Manifest-Σ.proj₂ (rec-fun r)
... | no  _ = Manifest-Σ.proj₁ (rec-fun r) · ℓ

------------------------------------------------------------------------
-- With

-- Sig With ℓ ≔ a is the signature Sig, but with the ℓ field set to a.

mutual

  infixl 5 _With_≔_

  _With_≔_ : ∀ {s} (Sig : Signature s) (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} →
             ((r : Restricted Sig ℓ ℓ∈) → Proj Sig ℓ r) → Signature s
  _With_≔_ ∅ ℓ {} a
  Sig , ℓ′ ∶ A With ℓ ≔ a with ℓ ≟ ℓ′
  ... | yes _ = Sig            , ℓ′ ≔ a
  ... | no  _ = Sig With ℓ ≔ a , ℓ′ ∶ A ∘ drop-With
  Sig , ℓ′ ≔ a′ With ℓ ≔ a with ℓ ≟ ℓ′
  ... | yes _ = Sig            , ℓ′ ≔ a
  ... | no  _ = Sig With ℓ ≔ a , ℓ′ ≔ a′ ∘ drop-With

  drop-With : ∀ {s} {Sig : Signature s} {ℓ : Label} {ℓ∈ : ℓ ∈ Sig}
              {a : (r : Restricted Sig ℓ ℓ∈) → Proj Sig ℓ r} →
              Record (Sig With ℓ ≔ a) → Record Sig
  drop-With {Sig = ∅} {ℓ∈ = ()}      r
  drop-With {Sig = Sig , ℓ′ ∶ A} {ℓ} r with ℓ ≟ ℓ′
  ... | yes _ = rec (proj₁ (rec-fun r) , proj₂ (rec-fun r))
                where open Manifest-Σ
  ... | no  _ = rec ( drop-With (Σ.proj₁ (rec-fun r))
                    , Σ.proj₂ (rec-fun r)
                    )
  drop-With {Sig = Sig , ℓ′ ≔ a} {ℓ} r with ℓ ≟ ℓ′
  ... | yes _ = rec (Manifest-Σ.proj₁ (rec-fun r) ,)
  ... | no  _ = rec (drop-With (Manifest-Σ.proj₁ (rec-fun r)) ,)
