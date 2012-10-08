{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.conv.coerce:0 -v tc.with:25 #-}

module FilterSub where

open import Common.Level
open import Common.Equality

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {a}{A : Set a} → Bool → A → A → A
if true  then t else e = t
if false then t else e = e

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

data Any {a p} {A : Set a}
         (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

infix 4 _⊆_ _∈_

_∈_ : ∀ {a}{A : Set a} → A → List A → Set _
x ∈ xs = Any (_≡_ x) xs

_⊆_ : ∀ {a}{A : Set a} → List A → List A → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false =     filter p xs

filter-⊆ : ∀ {a} {A : Set a} (p : A → Bool) →
           (xs : List A) → filter p xs ⊆ xs
filter-⊆ _ []       = λ ()
filter-⊆ p (x ∷ xs) with p x | filter-⊆ p xs
... | false | hyp = there ∘ hyp
... | true  | hyp =
  λ { (here  eq)      → here eq
    ; (there ∈filter) → there (hyp ∈filter)
    }
