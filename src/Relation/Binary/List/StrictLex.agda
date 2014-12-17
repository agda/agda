------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a strict partial order. The lexicographic
-- ordering itself can be either strict or non-strict, depending on
-- the value of a parameter.

module Relation.Binary.List.StrictLex where

open import Data.Empty
open import Data.Unit.Minimal using (⊤; tt)
open import Function
open import Data.Product
open import Data.Sum
open import Data.List
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.List.Pointwise as Pointwise
   using ([]; _∷_; head; tail)

module _ {A : Set} where

  data Lex (P : Set) (_≈_ _<_ : Rel A zero) : Rel (List A) zero where
    base : P                             → Lex P _≈_ _<_ []       []
    halt : ∀ {y ys}                      → Lex P _≈_ _<_ []       (y ∷ ys)
    this : ∀ {x xs y ys} (x<y : x < y)   → Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)
    next : ∀ {x xs y ys} (x≈y : x ≈ y)
           (xs⊴ys : Lex P _≈_ _<_ xs ys) → Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)

  -- Strict lexicographic ordering.

  Lex-< : (_≈_ _<_ : Rel A zero) → Rel (List A) zero
  Lex-< = Lex ⊥

  ¬[]<[] : ∀ {_≈_ _<_} → ¬ Lex-< _≈_ _<_ [] []
  ¬[]<[] (base ())

  -- Non-strict lexicographic ordering.

  Lex-≤ : (_≈_ _<_ : Rel A zero) → Rel (List A) zero
  Lex-≤ = Lex ⊤

  -- Utilities.

  ¬≤-this : ∀ {P _≈_ _<_ x y xs ys} → ¬ (x ≈ y) → ¬ (x < y) →
            ¬ Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)
  ¬≤-this ¬x≈y ¬x<y (this x<y)       = ¬x<y x<y
  ¬≤-this ¬x≈y ¬x<y (next x≈y xs⊴ys) = ¬x≈y x≈y

  ¬≤-next : ∀ {P _≈_ _<_ x y xs ys} →
            ¬ (x < y) → ¬ Lex P _≈_ _<_ xs ys →
            ¬ Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)
  ¬≤-next ¬x<y ¬xs⊴ys (this x<y)       = ¬x<y x<y
  ¬≤-next ¬x<y ¬xs⊴ys (next x≈y xs⊴ys) = ¬xs⊴ys xs⊴ys

  ----------------------------------------------------------------------
  -- Properties

  ≤-reflexive : ∀ _≈_ _<_ → Pointwise.Rel _≈_ ⇒ Lex-≤ _≈_ _<_
  ≤-reflexive _≈_ _<_ []            = base tt
  ≤-reflexive _≈_ _<_ (x≈y ∷ xs≈ys) =
    next x≈y (≤-reflexive _≈_ _<_ xs≈ys)

  <-irreflexive : ∀ {_≈_ _<_} → Irreflexive _≈_ _<_ →
                  Irreflexive (Pointwise.Rel _≈_) (Lex-< _≈_ _<_)
  <-irreflexive irr []            (base ())
  <-irreflexive irr (x≈y ∷ xs≈ys) (this x<y)       = irr x≈y x<y
  <-irreflexive irr (x≈y ∷ xs≈ys) (next x≊y xs⊴ys) =
    <-irreflexive irr xs≈ys xs⊴ys

  transitive : ∀ {P _≈_ _<_} →
               IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
               Transitive (Lex P _≈_ _<_)
  transitive {P} {_≈_} {_<_} eq resp tr = trans
    where
    trans : Transitive (Lex P _≈_ _<_)
    trans (base p)         (base _)         = base p
    trans (base y)         halt             = halt
    trans halt             (this y<z)       = halt
    trans halt             (next y≈z ys⊴zs) = halt
    trans (this x<y)       (this y<z)       = this (tr x<y y<z)
    trans (this x<y)       (next y≈z ys⊴zs) = this (proj₁ resp y≈z x<y)
    trans (next x≈y xs⊴ys) (this y<z)       =
       this (proj₂ resp (IsEquivalence.sym eq x≈y) y<z)
    trans (next x≈y xs⊴ys) (next y≈z ys⊴zs) =
       next (IsEquivalence.trans eq x≈y y≈z) (trans xs⊴ys ys⊴zs)

  antisymmetric :
    ∀ {P _≈_ _<_} →
    Symmetric _≈_ → Irreflexive _≈_ _<_ →  Asymmetric _<_ →
    Antisymmetric (Pointwise.Rel _≈_) (Lex P _≈_ _<_)
  antisymmetric {P} {_≈_} {_<_} sym ir asym = as
    where
    as : Antisymmetric (Pointwise.Rel _≈_) (Lex P _≈_ _<_)
    as (base _)         (base _)         = []
    as halt             ()
    as (this x<y)       (this y<x)       = ⊥-elim (asym x<y y<x)
    as (this x<y)       (next y≈x ys⊴xs) = ⊥-elim (ir (sym y≈x) x<y)
    as (next x≈y xs⊴ys) (this y<x)       = ⊥-elim (ir (sym x≈y) y<x)
    as (next x≈y xs⊴ys) (next y≈x ys⊴xs) = x≈y ∷ as xs⊴ys ys⊴xs

  <-asymmetric : ∀ {_≈_ _<_} →
                 Symmetric _≈_ → _<_ Respects₂ _≈_ → Asymmetric _<_ →
                 Asymmetric (Lex-< _≈_ _<_)
  <-asymmetric {_≈_} {_<_} sym resp as = asym
    where
    irrefl : Irreflexive _≈_ _<_
    irrefl = asym⟶irr resp sym as

    asym : Asymmetric (Lex-< _≈_ _<_)
    asym (base bot)       _                = bot
    asym halt             ()
    asym (this x<y)       (this y<x)       = as x<y y<x
    asym (this x<y)       (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
    asym (next x≈y xs⊴ys) (this y<x)       = irrefl (sym x≈y) y<x
    asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

  respects₂ : ∀ {P _≈_ _<_} →
              IsEquivalence _≈_ → _<_ Respects₂ _≈_ →
              Lex P _≈_ _<_ Respects₂ Pointwise.Rel _≈_
  respects₂ {P} {_≈_} {_<_} eq resp =
    (λ {xs} {ys} {zs} → resp¹ {xs} {ys} {zs}) ,
    (λ {xs} {ys} {zs} → resp² {xs} {ys} {zs})
    where
    resp¹ : ∀ {xs} → Lex P _≈_ _<_ xs Respects Pointwise.Rel _≈_
    resp¹ []            xs⊴[]            = xs⊴[]
    resp¹ (x≈y ∷ xs≈ys) halt             = halt
    resp¹ (x≈y ∷ xs≈ys) (this z<x)       = this (proj₁ resp x≈y z<x)
    resp¹ (x≈y ∷ xs≈ys) (next z≈x zs⊴xs) =
      next (Eq.trans z≈x x≈y) (resp¹ xs≈ys zs⊴xs)
      where module Eq = IsEquivalence eq

    resp² : ∀ {ys} → flip (Lex P _≈_ _<_) ys Respects Pointwise.Rel _≈_
    resp² []            []⊴ys            = []⊴ys
    resp² (x≈z ∷ xs≈zs) (this x<y)       = this (proj₂ resp x≈z x<y)
    resp² (x≈z ∷ xs≈zs) (next x≈y xs⊴ys) =
      next (Eq.trans (Eq.sym x≈z) x≈y) (resp² xs≈zs xs⊴ys)
      where module Eq = IsEquivalence eq

  decidable : ∀ {P _≈_ _<_} →
              Dec P → Decidable _≈_ → Decidable _<_ →
              Decidable (Lex P _≈_ _<_)
  decidable (yes p) dec-≈ dec-< []       []       = yes (base p)
  decidable (no ¬p) dec-≈ dec-< []       []       = no λ{(base p) → ¬p p}
  decidable dec-P   dec-≈ dec-< []       (y ∷ ys) = yes halt
  decidable dec-P   dec-≈ dec-< (x ∷ xs) []       = no (λ ())
  decidable dec-P   dec-≈ dec-< (x ∷ xs) (y ∷ ys) with dec-< x y
  ... | yes x<y = yes (this x<y)
  ... | no ¬x<y with dec-≈ x y
  ...           | no ¬x≈y = no (¬≤-this ¬x≈y ¬x<y)
  ...           | yes x≈y with decidable dec-P dec-≈ dec-< xs ys
  ...                     | yes xs⊴ys = yes (next x≈y xs⊴ys)
  ...                     | no ¬xs⊴ys = no (¬≤-next ¬x<y ¬xs⊴ys)

  <-decidable :
    ∀ {_≈_ _<_} →
    Decidable _≈_ → Decidable _<_ → Decidable (Lex-< _≈_ _<_)
  <-decidable = decidable (no id)

  ≤-decidable :
    ∀ {_≈_ _<_} →
    Decidable _≈_ → Decidable _<_ → Decidable (Lex-≤ _≈_ _<_)
  ≤-decidable = decidable (yes tt)

  -- Note that trichotomy is an unnecessarily strong precondition for
  -- the following lemma.

  ≤-total :
    ∀ {_≈_ _<_} →
    Symmetric _≈_ → Trichotomous _≈_ _<_ → Total (Lex-≤ _≈_ _<_)
  ≤-total {_≈_} {_<_} sym tri = total
    where
    total : Total (Lex-≤ _≈_ _<_)
    total []       []       = inj₁ (base tt)
    total []       (x ∷ xs) = inj₁ halt
    total (x ∷ xs) []       = inj₂ halt
    total (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y _ _ = inj₁ (this x<y)
    ... | tri> _ _ y<x = inj₂ (this y<x)
    ... | tri≈ _ x≈y _ with total xs ys
    ...                | inj₁ xs≲ys = inj₁ (next      x≈y  xs≲ys)
    ...                | inj₂ ys≲xs = inj₂ (next (sym x≈y) ys≲xs)

  <-compare : ∀ {_≈_ _<_} →
              Symmetric _≈_ → Trichotomous _≈_ _<_ →
              Trichotomous (Pointwise.Rel _≈_) (Lex-< _≈_ _<_)
  <-compare {_≈_} {_<_} sym tri = cmp
   where
   cmp : Trichotomous (Pointwise.Rel _≈_) (Lex-< _≈_ _<_)
   cmp []       []       = tri≈ ¬[]<[] [] ¬[]<[]
   cmp []       (y ∷ ys) = tri< halt (λ ()) (λ ())
   cmp (x ∷ xs) []       = tri> (λ ()) (λ ()) halt
   cmp (x ∷ xs) (y ∷ ys) with tri x y
   ... | tri< x<y ¬x≈y ¬y<x =
         tri< (this x<y) (¬x≈y ∘ head) (¬≤-this (¬x≈y ∘ sym) ¬y<x)
   ... | tri> ¬x<y ¬x≈y y<x =
         tri> (¬≤-this ¬x≈y ¬x<y) (¬x≈y ∘ head) (this y<x)
   ... | tri≈ ¬x<y x≈y ¬y<x with cmp xs ys
   ...    | tri< xs<ys ¬xs≈ys ¬ys<xs =
            tri< (next x≈y xs<ys) (¬xs≈ys ∘ tail) (¬≤-next ¬y<x ¬ys<xs)
   ...    | tri≈ ¬xs<ys xs≈ys ¬ys<xs =
            tri≈ (¬≤-next ¬x<y ¬xs<ys) (x≈y ∷ xs≈ys) (¬≤-next ¬y<x ¬ys<xs)
   ...    | tri> ¬xs<ys ¬xs≈ys ys<xs =
            tri> (¬≤-next ¬x<y ¬xs<ys) (¬xs≈ys ∘ tail) (next (sym x≈y) ys<xs)

  -- Some collections of properties which are preserved by Lex-≤ or
  -- Lex-<.

  ≤-isPreorder : ∀ {_≈_ _<_} →
                 IsEquivalence _≈_ → Transitive _<_ → _<_ Respects₂ _≈_ →
                 IsPreorder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isPreorder {_≈_} {_<_} eq tr resp = record
    { isEquivalence = Pointwise.isEquivalence eq
    ; reflexive     = ≤-reflexive _≈_ _<_
    ; trans         = transitive eq resp tr
    }

  ≤-isPartialOrder : ∀ {_≈_ _<_} →
                     IsStrictPartialOrder _≈_ _<_ →
                     IsPartialOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isPartialOrder {_≈_} {_<_} spo = record
    { isPreorder = ≤-isPreorder isEquivalence trans <-resp-≈
    ; antisym    = antisymmetric Eq.sym irrefl
                     (trans∧irr⟶asym {_≈_ = _≈_} {_<_ = _<_}
                                     Eq.refl trans irrefl)
    } where open IsStrictPartialOrder spo

  ≤-isTotalOrder : ∀ {_≈_ _<_} →
                   IsStrictTotalOrder _≈_ _<_ →
                   IsTotalOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isTotalOrder sto = record
    { isPartialOrder =
        ≤-isPartialOrder (record
          { isEquivalence = isEquivalence
          ; irrefl        = tri⟶irr <-resp-≈ Eq.sym compare
          ; trans         = trans
          ; <-resp-≈      = <-resp-≈
          })
    ; total          = ≤-total Eq.sym compare
    } where open IsStrictTotalOrder sto

  ≤-isDecTotalOrder : ∀ {_≈_ _<_} →
                      IsStrictTotalOrder _≈_ _<_ →
                      IsDecTotalOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isDecTotalOrder sto = record
    { isTotalOrder = ≤-isTotalOrder sto
    ; _≟_          = Pointwise.decidable _≟_
    ; _≤?_         = ≤-decidable _≟_ (tri⟶dec< compare)
    } where open IsStrictTotalOrder sto

  <-isStrictPartialOrder
    : ∀ {_≈_ _<_} → IsStrictPartialOrder _≈_ _<_ →
      IsStrictPartialOrder (Pointwise.Rel _≈_) (Lex-< _≈_ _<_)
  <-isStrictPartialOrder spo = record
    { isEquivalence = Pointwise.isEquivalence isEquivalence
    ; irrefl        = <-irreflexive irrefl
    ; trans         = transitive isEquivalence <-resp-≈ trans
    ; <-resp-≈      = respects₂ isEquivalence <-resp-≈
    } where open IsStrictPartialOrder spo

  <-isStrictTotalOrder
    : ∀ {_≈_ _<_} → IsStrictTotalOrder _≈_ _<_ →
      IsStrictTotalOrder (Pointwise.Rel _≈_) (Lex-< _≈_ _<_)
  <-isStrictTotalOrder sto = record
    { isEquivalence = Pointwise.isEquivalence isEquivalence
    ; trans         = transitive isEquivalence <-resp-≈ trans
    ; compare       = <-compare Eq.sym compare
    ; <-resp-≈      = respects₂ isEquivalence <-resp-≈
    } where open IsStrictTotalOrder sto

-- "Packages" (e.g. preorders) can also be handled.

≤-preorder : Preorder _ _ _ → Preorder _ _ _
≤-preorder pre = record
  { isPreorder = ≤-isPreorder isEquivalence trans ∼-resp-≈
  } where open Preorder pre

≤-partialOrder : StrictPartialOrder _ _ _ → Poset _ _ _
≤-partialOrder spo = record
  { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo

≤-decTotalOrder : StrictTotalOrder _ _ _ → DecTotalOrder _ _ _
≤-decTotalOrder sto = record
  { isDecTotalOrder = ≤-isDecTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto

<-strictPartialOrder :
  StrictPartialOrder _ _ _ → StrictPartialOrder _ _ _
<-strictPartialOrder spo = record
  { isStrictPartialOrder = <-isStrictPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo

<-strictTotalOrder : StrictTotalOrder _ _ _ → StrictTotalOrder _ _ _
<-strictTotalOrder sto = record
  { isStrictTotalOrder = <-isStrictTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto
