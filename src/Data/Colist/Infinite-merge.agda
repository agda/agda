------------------------------------------------------------------------
-- The Agda standard library
--
-- Infinite merge operation for coinductive lists
------------------------------------------------------------------------

module Data.Colist.Infinite-merge where

open import Coinduction
open import Data.Colist as Colist hiding (_⋎_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod
open import Data.Sum
open import Data.Sum.Relation.Pointwise
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Induction.Nat using (<′-wellFounded)
import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- Some code that is used to work around Agda's syntactic guardedness
-- checker.

private

  infixr 5 _∷_ _⋎_

  data ColistP {a} (A : Set a) : Set a where
    []  : ColistP A
    _∷_ : A → ∞ (ColistP A) → ColistP A
    _⋎_ : ColistP A → ColistP A → ColistP A

  data ColistW {a} (A : Set a) : Set a where
    []  : ColistW A
    _∷_ : A → ColistP A → ColistW A

  program : ∀ {a} {A : Set a} → Colist A → ColistP A
  program []       = []
  program (x ∷ xs) = x ∷ ♯ program (♭ xs)

  mutual

    _⋎W_ : ∀ {a} {A : Set a} → ColistW A → ColistP A → ColistW A
    []       ⋎W ys = whnf ys
    (x ∷ xs) ⋎W ys = x ∷ (ys ⋎ xs)

    whnf : ∀ {a} {A : Set a} → ColistP A → ColistW A
    whnf []        = []
    whnf (x ∷ xs)  = x ∷ ♭ xs
    whnf (xs ⋎ ys) = whnf xs ⋎W ys

  mutual

    ⟦_⟧P : ∀ {a} {A : Set a} → ColistP A → Colist A
    ⟦ xs ⟧P = ⟦ whnf xs ⟧W

    ⟦_⟧W : ∀ {a} {A : Set a} → ColistW A → Colist A
    ⟦ [] ⟧W     = []
    ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  mutual

    ⋎-homP : ∀ {a} {A : Set a} (xs : ColistP A) {ys} →
             ⟦ xs ⋎ ys ⟧P ≈ ⟦ xs ⟧P Colist.⋎ ⟦ ys ⟧P
    ⋎-homP xs = ⋎-homW (whnf xs) _

    ⋎-homW : ∀ {a} {A : Set a} (xs : ColistW A) ys →
             ⟦ xs ⋎W ys ⟧W ≈ ⟦ xs ⟧W Colist.⋎ ⟦ ys ⟧P
    ⋎-homW (x ∷ xs) ys = x ∷ ♯ ⋎-homP ys
    ⋎-homW []       ys = begin ⟦ ys ⟧P ∎
      where open ≈-Reasoning

  ⟦program⟧P : ∀ {a} {A : Set a} (xs : Colist A) →
               ⟦ program xs ⟧P ≈ xs
  ⟦program⟧P []       = []
  ⟦program⟧P (x ∷ xs) = x ∷ ♯ ⟦program⟧P (♭ xs)

  Any-⋎P : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
           Any P ⟦ program xs ⋎ ys ⟧P ↔ (Any P xs ⊎ Any P ⟦ ys ⟧P)
  Any-⋎P {P = P} xs {ys} =
    Any P ⟦ program xs ⋎ ys ⟧P                ↔⟨ Any-cong Inv.id (⋎-homP (program xs)) ⟩
    Any P (⟦ program xs ⟧P Colist.⋎ ⟦ ys ⟧P)  ↔⟨ Any-⋎ _ ⟩
    (Any P ⟦ program xs ⟧P ⊎ Any P ⟦ ys ⟧P)   ↔⟨ Any-cong Inv.id (⟦program⟧P _) ⊎-cong (_ ∎) ⟩
    (Any P xs ⊎ Any P ⟦ ys ⟧P)                ∎
    where open Related.EquationalReasoning

  index-Any-⋎P :
    ∀ {a p} {A : Set a} {P : A → Set p} xs {ys}
    (p : Any P ⟦ program xs ⋎ ys ⟧P) →
    index p ≥′ [ index , index ]′ (Inverse.to (Any-⋎P xs) ⟨$⟩ p)
  index-Any-⋎P xs p
    with       Any-resp      id  (⋎-homW (whnf (program xs)) _) p
       | index-Any-resp {f = id} (⋎-homW (whnf (program xs)) _) p
  index-Any-⋎P xs p | q | q≡p
    with Inverse.to (Any-⋎ ⟦ program xs ⟧P) ⟨$⟩ q
       |       index-Any-⋎ ⟦ program xs ⟧P      q
  index-Any-⋎P xs p | q | q≡p | inj₂ r | r≤q rewrite q≡p = r≤q
  index-Any-⋎P xs p | q | q≡p | inj₁ r | r≤q
    with       Any-resp      id  (⟦program⟧P xs) r
       | index-Any-resp {f = id} (⟦program⟧P xs) r
  index-Any-⋎P xs p | q | q≡p | inj₁ r | r≤q | s | s≡r
    rewrite s≡r | q≡p = r≤q

-- Infinite variant of _⋎_.

private

  merge′ : ∀ {a} {A : Set a} → Colist (A × Colist A) → ColistP A
  merge′ []               = []
  merge′ ((x , xs) ∷ xss) = x ∷ ♯ (program xs ⋎ merge′ (♭ xss))

merge : ∀ {a} {A : Set a} → Colist (A × Colist A) → Colist A
merge xss = ⟦ merge′ xss ⟧P

-- Any lemma for merge.

Any-merge :
  ∀ {a p} {A : Set a} {P : A → Set p} xss →
  Any P (merge xss) ↔ Any (λ { (x , xs) → P x ⊎ Any P xs }) xss
Any-merge {P = P} = λ xss → record
  { to         = P.→-to-⟶ (proj₁ ∘ to xss)
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = proj₂ ∘ to xss
    ; right-inverse-of = λ p → begin
        proj₁ (to xss (from p))  ≡⟨ from-injective _ _ (proj₂ (to xss (from p))) ⟩
        p                        ∎
    }
  }
  where
  open P.≡-Reasoning

  -- The from function.

  Q = λ { (x , xs) → P x ⊎ Any P xs }

  from : ∀ {xss} → Any Q xss → Any P (merge xss)
  from (here (inj₁ p))        = here p
  from (here (inj₂ p))        = there (Inverse.from (Any-⋎P _)  ⟨$⟩ inj₁ p)
  from (there {x = _ , xs} p) = there (Inverse.from (Any-⋎P xs) ⟨$⟩ inj₂ (from p))

  -- Some lemmas.

  drop-there :
    ∀ {a p} {A : Set a} {P : A → Set p} {x xs} {p q : Any P _} →
    _≡_ {A = Any P (x ∷ xs)} (there p) (there q) → p ≡ q
  drop-there P.refl = P.refl

  drop-inj₁ : ∀ {a b} {A : Set a} {B : Set b} {x y} →
              _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  drop-inj₁ P.refl = P.refl

  drop-inj₂ : ∀ {a b} {A : Set a} {B : Set b} {x y} →
              _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
  drop-inj₂ P.refl = P.refl

  -- The from function is injective.

  from-injective : ∀ {xss} (p₁ p₂ : Any Q xss) →
                   from p₁ ≡ from p₂ → p₁ ≡ p₂
  from-injective (here (inj₁ p))  (here (inj₁ .p)) P.refl = P.refl
  from-injective (here (inj₁ _))  (here (inj₂ _))  ()
  from-injective (here (inj₂ _))  (here (inj₁ _))  ()
  from-injective (here (inj₂ p₁)) (here (inj₂ p₂)) eq     =
    P.cong (here ∘ inj₂) $
    drop-inj₁ $
    Inverse.injective (Inv.sym (Any-⋎P _)) {x = inj₁ p₁} {y = inj₁ p₂} $
    drop-there eq
  from-injective (here (inj₁ _))  (there _)  ()
  from-injective (here (inj₂ p₁)) (there p₂) eq
    with Inverse.injective (Inv.sym (Any-⋎P _))
                           {x = inj₁ p₁} {y = inj₂ (from p₂)}
                           (drop-there eq)
  ... | ()
  from-injective (there _)  (here (inj₁ _))  ()
  from-injective (there p₁) (here (inj₂ p₂)) eq
    with Inverse.injective (Inv.sym (Any-⋎P _))
                           {x = inj₂ (from p₁)} {y = inj₁ p₂}
                           (drop-there eq)
  ... | ()
  from-injective (there {x = _ , xs} p₁) (there p₂) eq =
    P.cong there $
    from-injective p₁ p₂ $
    drop-inj₂ $
    Inverse.injective (Inv.sym (Any-⋎P xs))
                      {x = inj₂ (from p₁)} {y = inj₂ (from p₂)} $
    drop-there eq

  -- The to function (defined as a right inverse of from).

  Input = ∃ λ xss → Any P (merge xss)

  Pred : Input → Set _
  Pred (xss , p) = ∃ λ (q : Any Q xss) → from q ≡ p

  to : ∀ xss p → Pred (xss , p)
  to = λ xss p →
    WF.All.wfRec (WF.Inverse-image.wellFounded size <′-wellFounded) _
                 Pred step (xss , p)
    where
    size : Input → ℕ
    size (_ , p) = index p

    step : ∀ p → WF.WfRec (_<′_ on size) Pred p → Pred p
    step ([]             , ())      rec
    step ((x , xs) ∷ xss , here  p) rec = here (inj₁ p) , P.refl
    step ((x , xs) ∷ xss , there p) rec
      with Inverse.to (Any-⋎P xs) ⟨$⟩ p
         | Inverse.left-inverse-of (Any-⋎P xs) p
         | index-Any-⋎P xs p
    step ((x , xs) ∷ xss , there .(Inverse.from (Any-⋎P xs) ⟨$⟩ inj₁ q)) rec | inj₁ q | P.refl | _   = here (inj₂ q) , P.refl
    step ((x , xs) ∷ xss , there .(Inverse.from (Any-⋎P xs) ⟨$⟩ inj₂ q)) rec | inj₂ q | P.refl | q≤p =
      Prod.map there
               (P.cong (there ∘ _⟨$⟩_ (Inverse.from (Any-⋎P xs)) ∘ inj₂))
               (rec (♭ xss , q) (s≤′s q≤p))

-- Every member of xss is a member of merge xss, and vice versa (with
-- equal multiplicities).

∈-merge : ∀ {a} {A : Set a} {y : A} xss →
          y ∈ merge xss ↔ ∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs)
∈-merge {y = y} xss =
  y ∈ merge xss                                           ↔⟨ Any-merge _ ⟩
  Any (λ { (x , xs) → y ≡ x ⊎ y ∈ xs }) xss               ↔⟨ Any-∈ ⟩
  (∃ λ { (x , xs) → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs) })  ↔⟨ Σ-assoc ⟩
  (∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs))         ∎
  where open Related.EquationalReasoning
