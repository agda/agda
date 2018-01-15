------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductive pointwise lifting of relations to vectors
------------------------------------------------------------------------

module Data.Vec.Relation.InductivePointwise where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec as Vec hiding ([_]; head; tail; map; lookup)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

infixr 5 _∷_

data Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) :
                ∀ {n} (xs : Vec A n) (ys : Vec B n) → Set ℓ where
  []  : Pointwise _∼_ [] []
  _∷_ : ∀ {n x y} {xs : Vec A n} {ys : Vec B n}
        (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) →
        Pointwise _∼_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations

head : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
       {n x y xs} {ys : Vec B n} →
       Pointwise _~_ (x ∷ xs) (y ∷ ys) → x ~ y
head (x∼y ∷ xs∼ys) = x∼y

tail : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
       {n x y xs} {ys : Vec B n} →
       Pointwise _~_ (x ∷ xs) (y ∷ ys) → Pointwise _~_ xs ys
tail (x∼y ∷ xs∼ys) = xs∼ys

lookup : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
         {k xs ys} →  Pointwise _~_ xs ys →
         ∀ (i : Fin k) → (Vec.lookup i xs) ~ (Vec.lookup i ys)
lookup (x~y ∷ _)     zero    = x~y
lookup (_   ∷ xs~ys) (suc i) = lookup xs~ys i

-- Maps
module _ {a b} {A : Set a} {B : Set b} where

  map : ∀ {ℓ} {_~_ _~′_ : REL A B ℓ} {n} →
        _~_ ⇒ _~′_ → Pointwise _~_ ⇒ Pointwise _~′_ {n}
  map ~⇒~′ []             = []
  map ~⇒~′ (x∼y ∷ xs~ys) = ~⇒~′ x∼y ∷ map ~⇒~′ xs~ys

  gmap : ∀ {ℓ} {_~_ : Rel A ℓ} {_~′_ : Rel B ℓ} {f : A → B} {n} →
         _~_ =[ f ]⇒ _~′_ →
         Pointwise _~_ =[ Vec.map {n = n} f ]⇒ Pointwise _~′_
  gmap ~⇒~′ []             = []
  gmap ~⇒~′ (x∼y ∷ xs~ys) = ~⇒~′ x∼y ∷ gmap ~⇒~′ xs~ys

-- Appending
module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

  ++⁺ : ∀ {m n} {ws : Vec A m} {xs} {ys : Vec A n} {zs} →
        Pointwise _~_ ws xs → Pointwise _~_ ys zs →
        Pointwise _~_ (ws ++ ys) (xs ++ zs)
  ++⁺ []            ys~zs = ys~zs
  ++⁺ (w~x ∷ ws~xs) ys~zs = w~x ∷ (++⁺ ws~xs ys~zs)

  ++ˡ⁻ : ∀ {m n} (ws : Vec A m) xs {ys : Vec A n} {zs} →
         Pointwise _~_ (ws ++ ys) (xs ++ zs) → Pointwise _~_ ws xs
  ++ˡ⁻ []       []        _                    = []
  ++ˡ⁻ (w ∷ ws) (x ∷ xs) (w~x ∷ ps) = w~x ∷ ++ˡ⁻ ws xs ps

  ++ʳ⁻ : ∀ {m n} (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs} →
         Pointwise _~_ (ws ++ ys) (xs ++ zs) → Pointwise _~_ ys zs
  ++ʳ⁻ [] [] ys~zs = ys~zs
  ++ʳ⁻ (w ∷ ws) (x ∷ xs) (_ ∷ ps) = ++ʳ⁻ ws xs ps

  ++⁻ : ∀ {m n} (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs} →
        Pointwise _~_ (ws ++ ys) (xs ++ zs) →
        Pointwise _~_ ws xs × Pointwise _~_ ys zs
  ++⁻ ws xs ps = ++ˡ⁻ ws xs ps , ++ʳ⁻ ws xs ps

-- Concatenating
module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

  concat⁺ : ∀ {m n} {xss : Vec (Vec A m) n} {yss} →
            Pointwise (Pointwise _~_) xss yss →
            Pointwise _~_ (concat xss) (concat yss)
  concat⁺ [] = []
  concat⁺ (xs~ys ∷ ps) = ++⁺ xs~ys (concat⁺ ps)

  concat⁻ : ∀ {m n} (xss : Vec (Vec A m) n) yss →
            Pointwise _~_ (concat xss) (concat yss) →
            Pointwise (Pointwise _~_) xss yss
  concat⁻ []         []         [] = []
  concat⁻ (xs ∷ xss) (ys ∷ yss) ps =
    ++ˡ⁻ xs ys ps ∷ concat⁻ xss yss (++ʳ⁻ xs ys ps)

------------------------------------------------------------------------
-- Properties

-- REL properties preserved by Pointwise
sym : ∀ {a b ℓ} {A : Set a} {B : Set b}
      {P : REL A B ℓ} {Q : REL B A ℓ} {n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {n = n})
sym sm []             = []
sym sm (x∼y ∷ xs~ys) = sm x∼y ∷ sym sm xs~ys

trans : ∀ {a b c ℓ} {A : Set a} {B : Set b} {C : Set c}
        {P : REL A B ℓ} {Q : REL B C ℓ} {R : REL A C ℓ} {n} →
        Trans P Q R →
        Trans (Pointwise P) (Pointwise Q) (Pointwise R {n = n})
trans trns []             []             = []
trans trns (x∼y ∷ xs~ys) (y∼z ∷ ys~zs) =
  trns x∼y y∼z ∷ trans trns xs~ys ys~zs

decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} →
            Decidable _∼_ → ∀ {n} → Decidable (Pointwise _∼_ {n = n})
decidable dec []       []       = yes []
decidable dec (x ∷ xs) (y ∷ ys) with dec x y
... | no ¬x∼y = no (¬x∼y ∘ head)
... | yes x∼y with decidable dec xs ys
...   | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
...   | yes xs∼ys = yes (x∼y ∷ xs∼ys)

-- Rel properties preserved by Pointwise
module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  refl : ∀ {n} → Reflexive _~_ →
         Reflexive (Pointwise _~_ {n = n})
  refl ~-refl {[]}      = []
  refl ~-refl {x ∷ xs} = ~-refl ∷ refl ~-refl

  symmetric : ∀ {n} → Symmetric _~_ →
              Symmetric (Pointwise _~_ {n = n})
  symmetric = sym

  transitive : ∀ {n} → Transitive _~_ →
               Transitive (Pointwise _~_ {n = n})
  transitive = trans

  isEquivalence : ∀ {n} → IsEquivalence _~_ →
                  IsEquivalence (Pointwise _~_ {n = n})
  isEquivalence equiv = record
    { refl  = refl  (IsEquivalence.refl  equiv)
    ; sym   = sym   (IsEquivalence.sym   equiv)
    ; trans = trans (IsEquivalence.trans equiv)
    }

  isDecEquivalence : ∀ {n} → IsDecEquivalence _~_ →
                     IsDecEquivalence (Pointwise _~_ {n = n})
  isDecEquivalence decEquiv = record
    { isEquivalence = isEquivalence (IsDecEquivalence.isEquivalence decEquiv)
    ; _≟_           = decidable (IsDecEquivalence._≟_ decEquiv)
    }

-- Pointwise _≡_ is equivalent to _≡_
module _ {a} {A : Set a} where

  ≡⇒Pointwise-≡ : ∀ {n} {xs ys : Vec A n} →
                    Pointwise _≡_ xs ys → xs ≡ ys
  ≡⇒Pointwise-≡ []                = P.refl
  ≡⇒Pointwise-≡ (P.refl ∷ xs~ys) = P.cong (_ ∷_) (≡⇒Pointwise-≡ xs~ys)

  Pointwise-≡⇒≡ : ∀ {n} {xs ys : Vec A n} →
                     xs ≡ ys → Pointwise _≡_ xs ys
  Pointwise-≡⇒≡ P.refl = refl P.refl

  Pointwise-≡ : ∀ {n} {xs ys : Vec A n} →
                Pointwise _≡_ xs ys ⇔ xs ≡ ys
  Pointwise-≡ = equivalence ≡⇒Pointwise-≡ Pointwise-≡⇒≡

-- Degenerate cases where one side is ignored
module _ {a b ℓ} {A : Set a} {B : Set b} where
  open import Data.Vec.All

  Pointwiseˡ⇒All : ∀ {P : A → Set ℓ} {n} {xs : Vec A n} {ys : Vec B n} →
                   Pointwise (λ x y → P x) xs ys → All P xs
  Pointwiseˡ⇒All []       = []
  Pointwiseˡ⇒All (p ∷ ps) = p ∷ Pointwiseˡ⇒All ps

  Pointwiseʳ⇒All : ∀ {P : B → Set ℓ} {n} {xs : Vec A n} {ys : Vec B n} →
                   Pointwise (λ x y → P y) xs ys → All P ys
  Pointwiseʳ⇒All []       = []
  Pointwiseʳ⇒All (p ∷ ps) = p ∷ Pointwiseʳ⇒All ps

  All⇒Pointwiseˡ : ∀ {P : A → Set ℓ} {n} {xs : Vec A n} {ys : Vec B n} →
                   All P xs → Pointwise (λ x y → P x) xs ys
  All⇒Pointwiseˡ {ys = []}    []       = []
  All⇒Pointwiseˡ {ys = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseˡ ps

  All⇒Pointwiseʳ : ∀ {P : B → Set ℓ} {n} {xs : Vec A n} {ys : Vec B n} →
                   All P ys → Pointwise (λ x y → P y) xs ys
  All⇒Pointwiseʳ {xs = []}    []       = []
  All⇒Pointwiseʳ {xs = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseʳ ps
