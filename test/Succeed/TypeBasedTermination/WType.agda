-- Tests W-types with heavy use of type aliases
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.WType where

WfRec : {A : Set} → (A → A → Set) → (A → Set) → (A → Set)
WfRec _<_ P x = ∀ y → y < x → P y

data Acc {A : Set} (_<_ : A → A → Set) (x : A) : Set where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

acc-inverse : ∀ {A : Set} {_<_ : A → A → Set} {x : A} (q : Acc _<_ x) →
              (y : A) → y < x → Acc _<_ y
acc-inverse (acc rs) y y<x = rs y y<x

_∈_ : {A : Set} → A → (A → Set) → Set
x ∈ P = P x

_⊆′_ : {A : Set} → (A → Set) → (A → Set) → Set
P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

RecStruct : Set → Set₁
RecStruct A = (A → Set) → (A → Set)

SubsetRecursorBuilder : ∀ {A : Set} →
                        (A → Set) → RecStruct A → Set₁
SubsetRecursorBuilder Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ Rec P


SubsetRecursor : ∀ {A : Set} →
                 (A → Set) → RecStruct A → Set₁
SubsetRecursor Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ P

subsetBuild : ∀ {A : Set} {Q : (A → Set)} {Rec : RecStruct A} →
                SubsetRecursorBuilder Q Rec →
                SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

module Some {A : Set} {_<_ :  A → A → Set}  where

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_)
  wfRecBuilder P f x (acc rs) y y<x =
    f y (wfRecBuilder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRecBuilder

  unfold-wfRec : (P : A → Set) (f : WfRec _<_ P ⊆′ P) {x : A} (q : Acc _<_ x) →
                 wfRec P f x q ≡ f x (λ y y<x → wfRec P f y (acc-inverse q y y<x))
  unfold-wfRec P f (acc rs) = refl
