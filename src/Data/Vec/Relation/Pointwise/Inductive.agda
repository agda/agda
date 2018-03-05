------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductive pointwise lifting of relations to vectors
------------------------------------------------------------------------

module Data.Vec.Relation.Pointwise.Inductive where

open import Algebra.FunctionProperties
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec hiding ([_]; head; tail; map; lookup)
open import Data.Vec.All using (All; []; _∷_)
open import Level using (_⊔_)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

------------------------------------------------------------------------
-- Relation

infixr 5 _∷_

data Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) :
               ∀ {m n} (xs : Vec A m) (ys : Vec B n) → Set (a ⊔ b ⊔ ℓ)
               where
  []  : Pointwise _∼_ [] []
  _∷_ : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n}
        (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) →
        Pointwise _∼_ (x ∷ xs) (y ∷ ys)

length-equal : ∀ {a b m n ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
               {xs : Vec A m} {ys : Vec B n} →
               Pointwise _~_ xs ys → m ≡ n
length-equal []          = P.refl
length-equal (_ ∷ xs~ys) = P.cong suc (length-equal xs~ys)

------------------------------------------------------------------------
-- Operations

module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

  head : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
         Pointwise _~_ (x ∷ xs) (y ∷ ys) → x ~ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
         Pointwise _~_ (x ∷ xs) (y ∷ ys) → Pointwise _~_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  lookup : ∀ {n} {xs : Vec A n} {ys : Vec B n} → Pointwise _~_ xs ys →
           ∀ i → (Vec.lookup i xs) ~ (Vec.lookup i ys)
  lookup (x~y ∷ _)     zero    = x~y
  lookup (_   ∷ xs~ys) (suc i) = lookup xs~ys i

  map : ∀ {ℓ₂} {_≈_ : REL A B ℓ₂} →
        _≈_ ⇒ _~_ → ∀ {m n} → Pointwise _≈_ ⇒ Pointwise _~_ {m} {n}
  map ~₁⇒~₂ []             = []
  map ~₁⇒~₂ (x∼y ∷ xs~ys) = ~₁⇒~₂ x∼y ∷ map ~₁⇒~₂ xs~ys

------------------------------------------------------------------------
-- Relational properties

refl : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} →
       ∀ {n} → Reflexive _~_ → Reflexive (Pointwise _~_ {n})
refl ~-refl {[]}      = []
refl ~-refl {x ∷ xs} = ~-refl ∷ refl ~-refl

sym : ∀ {a b ℓ} {A : Set a} {B : Set b}
      {P : REL A B ℓ} {Q : REL B A ℓ} {m n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {m} {n})
sym sm []             = []
sym sm (x∼y ∷ xs~ys) = sm x∼y ∷ sym sm xs~ys

trans : ∀ {a b c ℓ} {A : Set a} {B : Set b} {C : Set c}
        {P : REL A B ℓ} {Q : REL B C ℓ} {R : REL A C ℓ} {m n o} →
        Trans P Q R →
        Trans (Pointwise P {m}) (Pointwise Q {n} {o}) (Pointwise R)
trans trns []             []             = []
trans trns (x∼y ∷ xs~ys) (y∼z ∷ ys~zs) =
  trns x∼y y∼z ∷ trans trns xs~ys ys~zs

decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} →
            Decidable _∼_ → ∀ {m n} → Decidable (Pointwise _∼_ {m} {n})
decidable dec []       []       = yes []
decidable dec []       (y ∷ ys) = no λ()
decidable dec (x ∷ xs) []       = no λ()
decidable dec (x ∷ xs) (y ∷ ys) with dec x y
... | no ¬x∼y = no (¬x∼y ∘ head)
... | yes x∼y with decidable dec xs ys
...   | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
...   | yes xs∼ys = yes (x∼y ∷ xs∼ys)

isEquivalence : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} →
                IsEquivalence _~_ → ∀ n →
                IsEquivalence (Pointwise _~_ {n})
isEquivalence equiv n = record
  { refl  = refl  (IsEquivalence.refl  equiv)
  ; sym   = sym   (IsEquivalence.sym   equiv)
  ; trans = trans (IsEquivalence.trans equiv)
  }

isDecEquivalence : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} →
                   IsDecEquivalence _~_ → ∀ n →
                   IsDecEquivalence (Pointwise _~_ {n})
isDecEquivalence decEquiv n = record
  { isEquivalence = isEquivalence (IsDecEquivalence.isEquivalence decEquiv) n
  ; _≟_           = decidable (IsDecEquivalence._≟_ decEquiv)
  }

setoid : ∀ {a ℓ} → Setoid a ℓ → ℕ → Setoid a (a ⊔ ℓ)
setoid S n = record
   { isEquivalence = isEquivalence (Setoid.isEquivalence S) n
   }

decSetoid : ∀ {a ℓ} → DecSetoid a ℓ → ℕ → DecSetoid a (a ⊔ ℓ)
decSetoid S n = record
   { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence S) n
   }

------------------------------------------------------------------------
-- map

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  map⁺ : ∀ {ℓ₁ ℓ₂} {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂}
         {f : A → C} {g : B → D} →
         (∀ {x y} → x ~₁ y → f x ~₂ g y) →
         ∀ {m n xs ys} → Pointwise _~₁_ {m} {n} xs ys →
         Pointwise _~₂_ (Vec.map f xs) (Vec.map g ys)
  map⁺ ~₁⇒~₂ []             = []
  map⁺ ~₁⇒~₂ (x∼y ∷ xs~ys) = ~₁⇒~₂ x∼y ∷ map⁺ ~₁⇒~₂ xs~ys

------------------------------------------------------------------------
-- _++_

module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

  ++⁺ : ∀ {m n p q}
        {ws : Vec A m} {xs : Vec B p} {ys : Vec A n} {zs : Vec B q} →
        Pointwise _~_ ws xs → Pointwise _~_ ys zs →
        Pointwise _~_ (ws ++ ys) (xs ++ zs)
  ++⁺ []            ys~zs = ys~zs
  ++⁺ (w~x ∷ ws~xs) ys~zs = w~x ∷ (++⁺ ws~xs ys~zs)

  ++ˡ⁻ : ∀ {m n}
         (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
         Pointwise _~_ (ws ++ ys) (xs ++ zs) → Pointwise _~_ ws xs
  ++ˡ⁻ []       []        _                    = []
  ++ˡ⁻ (w ∷ ws) (x ∷ xs) (w~x ∷ ps) = w~x ∷ ++ˡ⁻ ws xs ps

  ++ʳ⁻ : ∀ {m n}
         (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
         Pointwise _~_ (ws ++ ys) (xs ++ zs) → Pointwise _~_ ys zs
  ++ʳ⁻ [] [] ys~zs = ys~zs
  ++ʳ⁻ (w ∷ ws) (x ∷ xs) (_ ∷ ps) = ++ʳ⁻ ws xs ps

  ++⁻ : ∀ {m n}
        (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
        Pointwise _~_ (ws ++ ys) (xs ++ zs) →
        Pointwise _~_ ws xs × Pointwise _~_ ys zs
  ++⁻ ws xs ps = ++ˡ⁻ ws xs ps , ++ʳ⁻ ws xs ps

------------------------------------------------------------------------
-- concat

module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

  concat⁺ : ∀ {m n p q}
            {xss : Vec (Vec A m) n} {yss : Vec (Vec B p) q} →
            Pointwise (Pointwise _~_) xss yss →
            Pointwise _~_ (concat xss) (concat yss)
  concat⁺ []           = []
  concat⁺ (xs~ys ∷ ps) = ++⁺ xs~ys (concat⁺ ps)

  concat⁻ : ∀ {m n} (xss : Vec (Vec A m) n) (yss : Vec (Vec B m) n) →
            Pointwise _~_ (concat xss) (concat yss) →
            Pointwise (Pointwise _~_) xss yss
  concat⁻ []         []         [] = []
  concat⁻ (xs ∷ xss) (ys ∷ yss) ps =
    ++ˡ⁻ xs ys ps ∷ concat⁻ xss yss (++ʳ⁻ xs ys ps)

------------------------------------------------------------------------
-- Degenerate pointwise relations

module _ {a b ℓ} {A : Set a} {B : Set b} {P : A → Set ℓ} where

  Pointwiseˡ⇒All : ∀ {m n} {xs : Vec A m} {ys : Vec B n} →
                   Pointwise (λ x y → P x) xs ys → All P xs
  Pointwiseˡ⇒All []       = []
  Pointwiseˡ⇒All (p ∷ ps) = p ∷ Pointwiseˡ⇒All ps

  Pointwiseʳ⇒All : ∀ {n} {xs : Vec B n} {ys : Vec A n} →
                   Pointwise (λ x y → P y) xs ys → All P ys
  Pointwiseʳ⇒All []       = []
  Pointwiseʳ⇒All (p ∷ ps) = p ∷ Pointwiseʳ⇒All ps

  All⇒Pointwiseˡ : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                   All P xs → Pointwise (λ x y → P x) xs ys
  All⇒Pointwiseˡ {ys = []}    []       = []
  All⇒Pointwiseˡ {ys = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseˡ ps

  All⇒Pointwiseʳ : ∀ {n} {xs : Vec B n} {ys : Vec A n} →
                   All P ys → Pointwise (λ x y → P y) xs ys
  All⇒Pointwiseʳ {xs = []}    []       = []
  All⇒Pointwiseʳ {xs = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseʳ ps

------------------------------------------------------------------------
-- Pointwise _≡_ is equivalent to _≡_

module _ {a} {A : Set a} where

  Pointwise-≡⇒≡ : ∀ {n} {xs ys : Vec A n} →
                  Pointwise _≡_ xs ys → xs ≡ ys
  Pointwise-≡⇒≡ []               = P.refl
  Pointwise-≡⇒≡ (P.refl ∷ xs~ys) = P.cong (_ ∷_) (Pointwise-≡⇒≡ xs~ys)

  ≡⇒Pointwise-≡ : ∀ {n} {xs ys : Vec A n} →
                  xs ≡ ys → Pointwise _≡_ xs ys
  ≡⇒Pointwise-≡ P.refl = refl P.refl

  Pointwise-≡↔≡ : ∀ {n} {xs ys : Vec A n} →
                  Pointwise _≡_ xs ys ⇔ xs ≡ ys
  Pointwise-≡↔≡ = equivalence Pointwise-≡⇒≡ ≡⇒Pointwise-≡

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

Pointwise-≡ = Pointwise-≡↔≡
