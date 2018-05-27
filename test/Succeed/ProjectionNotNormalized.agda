-- Test case extracted from The Agda standard library
-- Properties related to Any

{-# OPTIONS --show-implicit #-}

module ProjectionNotNormalized where

open import Common.Level renaming (lsuc to suc)
open import Common.Product
open Σ public

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Carrier → Carrier → Set ℓ
    refl          : ∀ {x} → x ≈ x

open import Common.Equality

setoid : ∀ {a} → Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; refl          = refl
  }

pmap : ∀ {a b p q}
         {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
       (f : A → B) → (∀ {x} → P x → Q (f x)) →
       Σ A P → Σ B Q
pmap f g (x , y) = (f x , g y)

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- Any P xs means that at least one element in xs satisfies P.

data Any {a p} {A : Set a}
         (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- Map.

map : ∀ {a p q} {A : Set a} {P : A → Set p} → {Q : A → Set q} →
      (∀ {x} → P x → Q x) → ∀ {x} → Any P x → Any Q x
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

------------------------------------------------------------------------
-- List membership and some related definitions

module Membership {c ℓ : Level} (S : Setoid c ℓ) where

  open module S = Setoid S using (_≈_) renaming (Carrier to A)

  -- List membership.

  infix 4 _∈_

  _∈_ : A → List A → Set _
  x ∈ xs = Any (_≈_ x) xs

  -- Finds an element satisfying the predicate.

  find : ∀ {p} {P : A → Set p} {xs} →
         Any P xs → ∃ λ x → Σ (x ∈ xs) λ _ → P x
  find (here px)   = (_ , here S.refl , px)
  find (there pxs) = pmap (λ x → x) (pmap there (λ x → x)) (find pxs)

  lose : ∀ {p} {P : A → Set p} {x xs} →
         (resp : ∀ {x y} → x ≈ y → P x → P y) →
         x ∈ xs → P x → Any P xs
  lose resp x∈xs px = map (λ eq → resp eq px) x∈xs

-- The code above instantiated (and slightly changed) for
-- propositional equality, along with some additional definitions.

open module M {a} {A : Set a} = Membership (setoid A)
  hiding (lose)

lose : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       x ∈ xs → P x → Any P xs
lose {P = P} = M.lose (subst P)


------------------------------------------------------------------------
-- Some lemmas related to map, find and lose

-- Lemmas relating map and find.

find∘map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs : List A} (p : Any P xs) (f : ∀ {x} → P x → Q x) →
           find (map f p) ≡ pmap (λ x → x) (pmap (λ x → x) f) (find p)
find∘map (here  p) f = refl
find∘map (there p) f rewrite find∘map p f = refl

-- find satisfies a simple equality when the predicate is a
-- propositional equality.

find-∈ : ∀ {a} {A : Set a} {x : A} {xs : List A} (x∈xs : x ∈ xs) →
         find x∈xs ≡ (x , x∈xs , refl)
find-∈ (here refl)  = refl
find-∈ (there x∈xs) rewrite find-∈ x∈xs = refl

-- find and lose are inverses (more or less).

{-
find∘lose : ∀ {a p} {A : Set a} (P : A → Set p)
            {x : {!!}} {xs : List {!!}}
            (x∈xs : x ∈ xs) (pp : P x) →
            find {P = P} (lose x∈xs pp) ≡ (x , x∈xs , pp)
find∘lose P x∈xs p = {!!}
-}
find∘lose : ∀ {a p} {A : Set a} (P : A → Set p)
            {x : _} {xs : _}
            (x∈xs : x ∈ xs) (pp : P x) →
            find {P = P} (lose x∈xs pp) ≡ (x , x∈xs , pp)
find∘lose P x∈xs p
  rewrite find∘map x∈xs (λ y → subst P y p)
        | find-∈ x∈xs
        = refl

{- Problem WAS:

applySection
new  = ProjectionNotNormalized.Membership.S
ptel = EmptyTel
old  = ProjectionNotNormalized.Setoid
ts   = [[]r{Var 2 []},[]r{Var 1 []},[]r(Var 0 [])]
S.refl  :  {c ℓ : Level} (S : Setoid c ℓ) {x : Setoid.Carrier S} →
           (S Setoid.≈ x) x
 is projection like in argument 2 for type ProjectionNotNormalized.Setoid
A  :  {c ℓ : Level} (S : Setoid c ℓ) → Set c
 is projection like in argument 2 for type ProjectionNotNormalized.Setoid
_≈_  :  {c ℓ : Level} (S : Setoid c ℓ) →
        Setoid.Carrier S → Setoid.Carrier S → Set ℓ
 is projection like in argument 2 for type ProjectionNotNormalized.Setoid
applySection
new  = ProjectionNotNormalized.M
ptel = ExtendTel []r{El {getSort = Type (Max [Plus 0 (MetaLevel _224 [])]), unEl = MetaV _225 []}} (Abs "a" ExtendTel []r{El {getSort = Type (Max [Plus 1 (NeutralLevel (Var 0 []))]), unEl = Sort (Type (Max [Plus 0 (NeutralLevel (Var 0 []))]))}} (Abs "A" EmptyTel))
old  = ProjectionNotNormalized.Membership
ts   = [[]r{Var 1 []},[]r{Var 1 []},[]r(Def ProjectionNotNormalized.setoid [Apply []r{Var 1 []},Apply []r(Var 0 [])])]
conApp: constructor ProjectionNotNormalized.recCon-NOT-PRINTED with fields [ProjectionNotNormalized.Setoid.Carrier,ProjectionNotNormalized.Setoid._≈_,ProjectionNotNormalized.Setoid.refl] projected by ProjectionNotNormalized.Membership.S.Carrier
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Substitute.hs:82
-}
