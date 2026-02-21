{-# OPTIONS --local-rewriting --prop --without-K #-}

module LocalRewriteMonoid where

data _≡_ {A : Set} (x : A) : A → Prop where
  refl : x ≡ x
{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡_

variable
  A B C : Set

ap : ∀ (f : A → B) {x₁ x₂} → x₁ ≡ x₂ → f x₁ ≡ f x₂
ap f refl = refl

ap₂ : ∀ (f : A → B → C) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
ap₂ f refl refl = refl

ap-app : ∀ {f₁ f₂ : A → B} {x} → f₁ ≡ f₂ → f₁ x ≡ f₂ x
ap-app refl = refl

sym : ∀ {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_∙_ : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

postulate
  funext : ∀ {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

module Foo (Car : Set) (_◆_ : Car → Car → Car) (id : Car)
           (@rew ◆◆ : ∀ {x y z} → (x ◆ y) ◆ z ≡ x ◆ (y ◆ z))
           (@rew ◆id : ∀ {x} → x ◆ id ≡ x)
           (@rew id◆ : ∀ {x} → id ◆ x ≡ x)
           where
  foo : ∀ {x y} → ((id ◆ (x ◆ id)) ◆ y) ◆ id ≡ x ◆ y
  foo = refl

module List (A : Set) where
  data List : Set where
    []   : List
    _,-_ : A → List → List

  variable
    xs ys zs : List

  _++_ : List → List → List
  [] ++ ys        = ys
  (x ,- xs) ++ ys = x ,- (xs ++ ys)

  ++[] : ∀ {xs} → xs ++ [] ≡ xs
  ++[] {xs = []}      = refl
  ++[] {xs = x ,- xs} = ap (x ,-_) ++[]

  ++++ : ∀ {xs ys zs} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++++ {xs = []}      = refl
  ++++ {xs = x ,- xs} = ap (x ,-_) (++++ {xs = xs})

  PreDList : Set
  PreDList = List → List

  []D' : PreDList
  []D' xs = xs

  _++D'_ : PreDList → PreDList → PreDList
  (xsD ++D' ysD) zs = xsD (ysD zs)

  _,-D'_ : A → PreDList → PreDList
  (x ,-D' xsD) ys = x ,- xsD ys

  data CohDList : PreDList → Prop where
    []C   : CohDList []D'
    _,-C_ : ∀ x {xsD} → CohDList xsD → CohDList (x ,-D' xsD)

  record DList : Set where
    constructor _,_
    field
      pre : PreDList
      coh : CohDList pre
  open DList

  []D : DList
  []D .pre = []D'
  []D .coh = []C

  _++C_ : ∀ {xsD ysD} → CohDList xsD → CohDList ysD → CohDList (xsD ++D' ysD)
  []C         ++C ysC = ysC
  (x ,-C xsC) ++C ysC = x ,-C (xsC ++C ysC)

  _++D_ : DList → DList → DList
  (xsD ++D ysD) .pre = xsD .pre ++D' ysD .pre
  (xsD ++D ysD) .coh = xsD .coh ++C ysD .coh

  -- And now we can access the contents of Foo!
  open Foo DList _++D_ []D refl refl refl

  -- DList is actually isomorphic to List
  -- (Unimportant for the test, but for fun)
  pre≡ : ∀ {xsD ysD} → xsD .pre ≡ ysD .pre → xsD ≡ ysD
  pre≡ refl = refl

  to : DList → List
  to xsD = xsD .pre []

  from : List → DList
  from xs        .pre ys = xs ++ ys
  from []        .coh    = []C
  from (x ,- xs) .coh    = x ,-C (from xs .coh)

  to-from : ∀ {xs} → to (from xs) ≡ xs
  to-from = ++[]

  from-to : ∀ {xsD : DList} → from (to xsD) ≡ xsD
  from-to {xsD = xsD , xsC} = pre≡ (go xsC) where
    go : ∀ {xsD} (xsC : CohDList xsD) → from (to (xsD , xsC)) .pre ≡ xsD
    go []C         = refl
    go (x ,-C xsC) = funext λ ys → ap (x ,-_) (ap-app (go xsC))

