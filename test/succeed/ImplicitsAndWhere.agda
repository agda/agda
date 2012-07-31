-- Andreas, 2012-07-31

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.def.where:100 #-}

module ImplicitsAndWhere where

open import Common.Level

record Id {a} (A : Set a) : Set a where
  constructor mkId
  field appId : A → A

-- implicits and where

test : forall {a}{A : Set a} → Id A
test = mkId bla
  where bla : ∀ {A} → A → A
        bla x = x

-- named trailing implicits

data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {a}{A : Set a} → Bool → A → A → A
if true  then t else e = t
if false then t else e = e

test2 : Bool -> {A B : Set} → Set
test2 true  {A}     = A
test2 false {B = B} = B

-- with clause and implicits
-- (from the standard library)

open import Common.Equality

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

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

gfilter : ∀ {a b} {A : Set a} {B : Set b} →
          (A → Maybe B) → List A → List B
gfilter p []       = []
gfilter p (x ∷ xs) with p x
... | just y  = y ∷ gfilter p xs
... | nothing =     gfilter p xs

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p = gfilter (λ x → if p x then just x else nothing)

filter-⊆ : ∀ {a} {A : Set a} (p : A → Bool) →
           (xs : List A) → filter p xs ⊆ xs
filter-⊆ _ []       = λ ()
filter-⊆ p (x ∷ xs) with p x | filter-⊆ p xs
... | false | hyp = there ∘ hyp
... | true  | hyp =
  λ { (here  eq)      → here eq
    ; (there ∈filter) → there (hyp ∈filter)
    }

-- example 2: with implicit function space into data type

record ⊤ : Set where

true' : {x : ⊤} → Bool
true' = true

bla : Set
bla with true'
... | true  = Bool
... | false = Bool
