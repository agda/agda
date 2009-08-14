------------------------------------------------------------------------
-- Lexicographic ordering on lists.
------------------------------------------------------------------------

-- Lexicographic ordering on lists defined using a strict, asymmetric 
-- relation and an equivalence relation. The lexicographic ordering 
-- itself can be either strict or non-strict, depending on a parameter.

module Relation.Binary.List.StrictLex where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Function
open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.List.Pointwise as Pointwise
   using ([]; _∷_; List-Rel; List-head; List-tail)

private 
 module Dummy {a : Set} where
 
  data List-Lex (P : Set) (≈ < : Rel a) : Rel (List a) where
    base : P → List-Lex P ≈ < [] []
    halt : ∀ {y ys} → List-Lex P ≈ < [] (y ∷ ys)  
    this : ∀ {x xs y ys} → (x<y : < x y) → List-Lex P ≈ < (x ∷ xs) (y ∷ ys)
    next : ∀ {x xs y ys} → (x≈y : ≈ x y) → (xs⊴ys : List-Lex P ≈ < xs ys) → 
           List-Lex P ≈ < (x ∷ xs) (y ∷ ys)

  -- Strict Lexicographic ordering

  List-Lex-< : (≈ < : Rel a) → Rel (List a)
  List-Lex-< = List-Lex ⊥

  ¬[]<[] : ∀ {≈ <} → ¬ (List-Lex-< ≈ < [] [])
  ¬[]<[] (base ())

  -- Non-Strict Lexicographic ordering

  List-Lex-≤ : (≈ < : Rel a) → Rel (List a)
  List-Lex-≤ = List-Lex ⊤

  -- Utilities

  ¬≤-this : ∀ {P ≈ < x y xs ys} → ¬ (≈ x y) → ¬ (< x y) → 
            ¬ (List-Lex P ≈ < (x ∷ xs) (y ∷ ys))
  ¬≤-this ¬x≈y ¬x<y (this x<y) = ¬x<y x<y
  ¬≤-this ¬x≈y ¬x<y (next x≈y xs⊴ys) = ¬x≈y x≈y

  ¬≤-next : ∀ {P ≈ < x y xs ys} → ¬ (< x y) → ¬ (List-Lex P ≈ < xs ys) → 
            ¬ (List-Lex P ≈ < (x ∷ xs) (y ∷ ys))
  ¬≤-next ¬x<y ¬xs⊴ys (this x<y) = ¬x<y x<y
  ¬≤-next ¬x<y ¬xs⊴ys (next x≈y xs⊴ys) = ¬xs⊴ys xs⊴ys

  ------------------------------------------------------------------------
  -- Properties

  List-≤-reflexive : ∀ ≈ < → (List-Rel ≈) ⇒ (List-Lex-≤ ≈ <)
  List-≤-reflexive ≈ < [] = base tt
  List-≤-reflexive ≈ < (x≈y ∷ xs≈ys) = next x≈y (List-≤-reflexive ≈ < xs≈ys)

  List-<-irreflexive : ∀ {≈ <} → Irreflexive ≈ < → 
                     Irreflexive (List-Rel ≈) (List-Lex-< ≈ <)
  List-<-irreflexive irr [] (base ())
  List-<-irreflexive irr (x≈y ∷ xs≈ys) (this x<y) = irr x≈y x<y
  List-<-irreflexive irr (x≈y ∷ xs≈ys) (next x≊y xs⊴ys) = List-<-irreflexive irr xs≈ys xs⊴ys

  List-transitive : ∀ {P ≈ <} → IsEquivalence ≈ → < Respects₂ ≈ → Transitive < →
                    Transitive (List-Lex P ≈ <)
  List-transitive eq resp tr (base p) (base _) = base p
  List-transitive eq resp tr (base y) halt = halt
  List-transitive eq resp tr halt (this y<z) = halt
  List-transitive eq resp tr halt (next y≈z ys⊴zs) = halt
  List-transitive eq resp tr (this x<y) (this y<z) = this (tr x<y y<z)
  List-transitive eq resp tr (this x<y) (next y≈z ys⊴zs) = this (proj₁ resp y≈z x<y)
  List-transitive eq resp tr (next x≈y xs⊴ys) (this y<z) = 
     this (proj₂ resp (IsEquivalence.sym eq x≈y) y<z)
  List-transitive eq resp tr (next x≈y xs⊴ys) (next y≈z ys⊴zs) = 
     next (IsEquivalence.trans eq x≈y y≈z) (List-transitive eq resp tr xs⊴ys ys⊴zs)

  List-antisymmetric :
    ∀ {P ≈ <} → Symmetric ≈ → Irreflexive ≈ < →  Asymmetric < →
    Antisymmetric (List-Rel ≈) (List-Lex P ≈ <)
  List-antisymmetric sym ir asym (base _) (base _) = []
  List-antisymmetric sym ir asym halt ()
  List-antisymmetric sym ir asym (this x<y) (this y<x) = ⊥-elim (asym x<y y<x)
  List-antisymmetric sym ir asym (this x<y) (next y≈x ys⊴xs) = ⊥-elim (ir (sym y≈x) x<y)
  List-antisymmetric sym ir asym (next x≈y xs⊴ys) (this y<x) = ⊥-elim (ir (sym x≈y) y<x)
  List-antisymmetric sym ir asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = 
    x≈y ∷ List-antisymmetric sym ir asym xs⊴ys ys⊴xs

  List-<-asymmetric :
    ∀ {≈ <} → Symmetric ≈ → < Respects₂ ≈ → Asymmetric < → Asymmetric (List-Lex-< ≈ <)
  List-<-asymmetric {≈} {<} sym resp as = asym
    where 
      irrefl : Irreflexive ≈ <
      irrefl = asym⟶irr resp sym as       

      asym : Asymmetric (List-Lex-< ≈ <)
      asym (base bot) _ = bot
      asym halt ()
      asym (this x<y) (this y<x) = as x<y y<x
      asym (this x<y) (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
      asym (next x≈y xs⊴ys) (this y<x) = irrefl (sym x≈y) y<x
      asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

  List-≈-respects₂ : 
    ∀ {P ≈ <} → IsEquivalence ≈ → < Respects₂ ≈ →
    (List-Lex P ≈ <) Respects₂ (List-Rel ≈)
  List-≈-respects₂ {P} {≈} {<} eq resp = 
   (λ {xs} {ys} {zs} → resp¹ {xs} {ys} {zs}) , 
   (λ {xs} {ys} {zs} → resp² {xs} {ys} {zs})
   where

    resp¹ : ∀ {xs} → (List-Lex P ≈ < xs) Respects (List-Rel ≈)
    resp¹ [] xs⊴[] = xs⊴[]
    resp¹ (x≈y ∷ xs≈ys) halt = halt
    resp¹ (x≈y ∷ xs≈ys) (this z<x) = this (proj₁ resp x≈y z<x)
    resp¹ (x≈y ∷ xs≈ys) (next z≈x zs⊴xs) = next (trans z≈x x≈y) (resp¹ xs≈ys zs⊴xs)
      where open IsEquivalence eq

    resp² : ∀ {ys} → (flip₁ (List-Lex P ≈ <) ys) Respects (List-Rel ≈)  
    resp² [] []⊴ys = []⊴ys
    resp² (x≈z ∷ xs≈zs) (this x<y) = this (proj₂ resp x≈z x<y)
    resp² (x≈z ∷ xs≈zs) (next x≈y xs⊴ys) = next (trans (sym x≈z) x≈y) (resp² xs≈zs xs⊴ys)
      where open IsEquivalence eq

  List-decidable : ∀ {P ≈ <} → Decidable ≈ → Decidable < →
                   Dec (List-Lex P ≈ < [] []) →
                   Decidable (List-Lex P ≈ <)
  List-decidable dec-≈ dec-< []≟[] [] [] = []≟[]
  List-decidable dec-≈ dec-< []≟[] [] (y ∷ ys) = yes halt
  List-decidable dec-≈ dec-< []≟[] (x ∷ xs) [] = no (λ ())
  List-decidable {P}{≈}{<} dec-≈ dec-< []≟[] (x ∷ xs) (y ∷ ys) with dec-< x y
  ... | yes x<y = yes (this x<y)
  ... | no ¬x<y with dec-≈ x y
  ...           | no ¬x≈y = no (¬≤-this ¬x≈y ¬x<y)
  ...           | yes x≈y with List-decidable dec-≈ dec-< []≟[] xs ys
  ...                     | yes xs⊴ys = yes (next x≈y xs⊴ys)
  ...                     | no ¬xs⊴ys = no (¬≤-next ¬x<y ¬xs⊴ys)

  List-<-decidable :  ∀ {≈ <} → Decidable ≈ → Decidable < →
                      Decidable (List-Lex-< ≈ <)
  List-<-decidable {≈} {<} dec-≈ dec-< = 
    List-decidable dec-≈ dec-< (no ¬[]<[])

  List-≤-decidable :  ∀ {≈ <} → Decidable ≈ → Decidable < →
                      Decidable (List-Lex-≤ ≈ <)
  List-≤-decidable {≈} {<} dec-≈ dec-< = 
    List-decidable dec-≈ dec-< (yes (base tt))

  -- List-Lex-≤ is total. TO DO: However, the trichotomous requirement is
  -- too strong. We merely need ≈ and < to be `jointly total.'

  List-≤-total : ∀ {≈ <} → Symmetric ≈ → Trichotomous ≈ < → Total (List-Lex-≤ ≈ <)
  List-≤-total sym tri [] [] = inj₁ (base tt)
  List-≤-total sym tri [] (x ∷ xs) = inj₁ halt
  List-≤-total sym tri (x ∷ xs) [] = inj₂ halt
  List-≤-total sym tri (x ∷ xs) (y ∷ ys) with tri x y
  ... | tri< x<y _ _ = inj₁ (this x<y) 
  ... | tri> _ _ y<x = inj₂ (this y<x)
  ... | tri≈ _ x≈y _ with List-≤-total sym tri xs ys
  ...                | inj₁ xs≲ys = inj₁ (next x≈y  xs≲ys)
  ...                | inj₂ ys≲xs = inj₂ (next (sym x≈y) ys≲xs)

  List-<-compare : ∀ {≈ <} → Symmetric ≈ → Trichotomous ≈ < → 
                 Trichotomous (List-Rel ≈) (List-Lex-< ≈ <)
  List-<-compare {≈}{<} sym tri = cmp
   where cmp : Trichotomous (List-Rel ≈) (List-Lex-< ≈ <)
         cmp [] [] = tri≈ ¬[]<[] [] ¬[]<[]
         cmp [] (y ∷ ys) = tri< halt (λ ()) (λ ())
         cmp (x ∷ xs) [] = tri> (λ ()) (λ ()) halt
         cmp (x ∷ xs) (y ∷ ys) with tri x y
         ... | tri< x<y ¬x≈y ¬y<x = 
               tri< (this x<y) (¬x≈y ∘ List-head) (¬≤-this (¬x≈y ∘ sym) ¬y<x)
         ... | tri> ¬x<y ¬x≈y y<x = 
               tri> (¬≤-this ¬x≈y ¬x<y) (¬x≈y ∘ List-head) (this y<x)
         ... | tri≈ ¬x<y x≈y ¬y<x with cmp xs ys
         ...    | tri< xs<ys ¬xs≈ys ¬ys<xs = 
                  tri< (next x≈y xs<ys) (¬xs≈ys ∘ List-tail) (¬≤-next ¬y<x ¬ys<xs)
         ...    | tri≈ ¬xs<ys xs≈ys ¬ys<xs = 
                  tri≈ (¬≤-next ¬x<y ¬xs<ys) (x≈y ∷ xs≈ys) (¬≤-next ¬y<x ¬ys<xs)
         ...    | tri> ¬xs<ys ¬xs≈ys ys<xs = 
                  tri> (¬≤-next ¬x<y ¬xs<ys) (¬xs≈ys ∘ List-tail) (next (sym x≈y) ys<xs)

  -- Some collections of properties which are preserved by List-Lex.

  -- List-≤-isPreorder does not take IsPreorder ≈ < as an argument because
  -- we do not demand < to be reflexive (nor irreflexive).
  
  List-≤-isPreorder : ∀ {≈ <} → IsEquivalence ≈ → Transitive < → < Respects₂ ≈ →
                    IsPreorder (List-Rel ≈) (List-Lex-≤ ≈ <)
  List-≤-isPreorder {≈} {<} eq tr resp = record
    { isEquivalence = Pointwise.List-isEquivalence eq
    ; reflexive = λ {xs ys} → List-≤-reflexive ≈ < {xs} {ys}
    ; trans = λ {xs ys zs} → 
              List-transitive eq resp tr {xs} {ys} {zs}
    ; ∼-resp-≈ = List-≈-respects₂ eq resp
    }

  List-≤-isPartialOrder :
    ∀ {≈ <} → IsStrictPartialOrder ≈ < → 
    IsPartialOrder (List-Rel ≈) (List-Lex-≤ ≈ <)
  List-≤-isPartialOrder {≈} {<} spo = record
    { isPreorder = List-≤-isPreorder isEquivalence trans <-resp-≈
    ; antisym = List-antisymmetric (IsEquivalence.sym isEquivalence) 
                                   irrefl 
                                   (trans∧irr⟶asym {≈ = ≈} {<}
                                     (IsEquivalence.refl isEquivalence)
                                     trans irrefl)
    }
    where open IsStrictPartialOrder spo

  List-≤-isTotalOrder : 
    ∀ {≈ <} → IsStrictTotalOrder ≈ < → 
    IsTotalOrder (List-Rel ≈) (List-Lex-≤ ≈ <)
  List-≤-isTotalOrder sto = record
    { isPartialOrder = 
        List-≤-isPartialOrder (record {
            isEquivalence = isEquivalence
          ; irrefl = tri⟶irr <-resp-≈ (IsEquivalence.sym isEquivalence) compare
          ; trans = trans
          ; <-resp-≈ = <-resp-≈
          })
    ; total = List-≤-total (IsEquivalence.sym isEquivalence) compare
    }
    where open IsStrictTotalOrder sto

  List-≤-isDecTotalOrder :
    ∀ {≈ <} → IsStrictTotalOrder ≈ < →
    IsDecTotalOrder (List-Rel ≈) (List-Lex-≤ ≈ <)
  List-≤-isDecTotalOrder sto = record
    { isTotalOrder = List-≤-isTotalOrder sto
    ; _≟_ = Pointwise.List-decidable _≟_
    ; _≤?_ = List-≤-decidable _≟_ (tri⟶dec< compare)
    } 
    where open IsStrictTotalOrder sto

  List-<-isStrictPartialOrder : 
    ∀ {≈ <} → IsStrictPartialOrder ≈ < → 
    IsStrictPartialOrder (List-Rel ≈) (List-Lex-< ≈ <)
  List-<-isStrictPartialOrder spo = record
    { isEquivalence = Pointwise.List-isEquivalence isEquivalence
    ; irrefl = λ {xs ys} → List-<-irreflexive irrefl
    ; trans = λ {xs ys zs} → List-transitive isEquivalence <-resp-≈ trans
    ; <-resp-≈ = List-≈-respects₂ isEquivalence <-resp-≈
    }         
    where open IsStrictPartialOrder spo

  List-<-isStrictTotalOrder :
    ∀ {≈ <} → IsStrictTotalOrder ≈ < →
    IsStrictTotalOrder (List-Rel ≈) (List-Lex-< ≈ <)
  List-<-isStrictTotalOrder sto = record
    { isEquivalence = Pointwise.List-isEquivalence isEquivalence
    ; trans = λ {xs ys zs} → List-transitive isEquivalence <-resp-≈ trans
    ; compare = List-<-compare Eq.sym compare
    ; <-resp-≈ = List-≈-respects₂ isEquivalence <-resp-≈
    }         
    where open IsStrictTotalOrder sto

open Dummy public

-- "Packages" (e.g. preorders) can also be combined.

List-≤-preorder : Preorder → Preorder
List-≤-preorder pre = record
  { isPreorder = List-≤-isPreorder (isEquivalence p) (trans p) (∼-resp-≈ p)
  }
  where open IsPreorder
        p = Preorder.isPreorder pre

List-≤-partialOrder : StrictPartialOrder → Poset
List-≤-partialOrder spo = record
  { isPartialOrder = List-≤-isPartialOrder isStrictPartialOrder
  }
  where open StrictPartialOrder spo

List-≤-totalOrder : StrictTotalOrder → TotalOrder
List-≤-totalOrder sto = record 
  { isTotalOrder = List-≤-isTotalOrder isStrictTotalOrder
  }
  where open StrictTotalOrder sto

List-≤-decTotalOrder : StrictTotalOrder → DecTotalOrder
List-≤-decTotalOrder sto = record 
  { isDecTotalOrder = List-≤-isDecTotalOrder isStrictTotalOrder
  }
  where open StrictTotalOrder sto

List-<-strictPartialOrder : StrictPartialOrder → StrictPartialOrder
List-<-strictPartialOrder spo = record
  { isStrictPartialOrder = List-<-isStrictPartialOrder isStrictPartialOrder
  }
  where open StrictPartialOrder spo

List-<-strictTotalOrder : StrictTotalOrder → StrictTotalOrder
List-<-strictTotalOrder sto = record
  { isStrictTotalOrder = List-<-isStrictTotalOrder isStrictTotalOrder
  }
  where open StrictTotalOrder sto