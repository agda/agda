module Rewrite where

open import Common.Equality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

plus-zero : ∀ n → n + zero ≡ n
plus-zero zero    = refl
plus-zero (suc n) rewrite plus-zero n = refl

plus-suc : ∀ n m → n + suc m ≡ suc (n + m)
plus-suc zero    m = refl
plus-suc (suc n) m rewrite plus-suc n m = refl

-- Proving things about functions using rewrite
data IsRefl {A : Set}{x : A} : ∀ {y} → x ≡ y → Set where
  isRefl : IsRefl refl

plus-suc-isrefl : ∀ {n m} → IsRefl (plus-suc n m)
plus-suc-isrefl {zero } {m} = isRefl
plus-suc-isrefl {suc n} {m} rewrite plus-suc n m = isRefl

-- Multiple rewrites
com : ∀ n m → n + m ≡ m + n
com n zero    = plus-zero _
com n (suc m) rewrite plus-suc n m
                    | com n m
              = refl

-- rewrite followed by with
thm : ∀ a b c → a + (b + c) ≡ (c + b) + a
thm a b c rewrite com b c with c + b
... | cb = com a cb

data List A : Set where
  [] : List A
  _∷_ : (x : A)(xs : List A) → List A

infixr 30 _∷_ _++_

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- rewrite in parameterised module
module ListProps {A : Set} where

  append-nil : (xs : List A) → xs ++ [] ≡ xs
  append-nil []       = refl
  append-nil (x ∷ xs) rewrite append-nil xs = refl

  append-assoc : (as bs cs : List A) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
  append-assoc []       bs cs = refl
  append-assoc (a ∷ as) bs cs rewrite append-assoc as bs cs = refl

  -- With implicit arguments
  append-assoc′ : ∀ (as : List A) {bs cs} → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
  append-assoc′ []       = refl
  append-assoc′ (a ∷ as) {bs}{cs} rewrite append-assoc′ as {bs} {cs} = refl

  reverse : List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ++ x ∷ []

  reverse-append : ∀ as bs → reverse (as ++ bs) ≡ reverse bs ++ reverse as
  reverse-append []       bs rewrite append-nil (reverse bs) = refl
  reverse-append (a ∷ as) bs rewrite reverse-append as bs
                          = append-assoc (reverse bs) _ _

  reverse-reverse : ∀ as → reverse (reverse as) ≡ as
  reverse-reverse []       = refl
  reverse-reverse (a ∷ as) rewrite reverse-append (reverse as) (a ∷ [])
                                 | reverse-reverse as
                           = refl

open ListProps

map : ∀ {A B} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_∘_ : {A : Set}{B : A → Set}{C : ∀ x → B x → Set}
      (f : ∀ {x} (y : B x) → C x y)(g : ∀ x → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

id : {A : Set} → A → A
id x = x

map-id : ∀ {A} (xs : List A) → map id xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) rewrite map-id xs = refl

map-compose : ∀ {A B C} (f : B → C)(g : A → B)(xs : List A) →
              map (f ∘ g) xs ≡ (map f ∘ map g) xs
map-compose f g []       = refl
map-compose f g (x ∷ xs) rewrite map-compose f g xs = refl

map-append : ∀ {A B} (f : A → B) (xs ys : List A) →
             map f (xs ++ ys) ≡ map f xs ++ map f ys
map-append f []       ys = refl
map-append f (x ∷ xs) ys rewrite map-append f xs ys = refl

map-reverse : ∀ {A B} (f : A → B) (xs : List A) →
              map f (reverse xs) ≡ reverse (map f xs)
map-reverse f []       = refl
map-reverse f (x ∷ xs) rewrite map-append f (reverse xs) (x ∷ [])
                             | map-reverse f xs
                       = refl

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

module FoldAssoc
  {A : Set}(_∙_ : A → A → A)
  (assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)) where

  smashr = foldr _∙_
  smashl = foldl _∙_

  foldr-append : ∀ ∅ z xs ys → (∀ x → ∅ ∙ x ≡ x) →
                 smashr z (xs ++ ys) ≡ smashr ∅ xs ∙ smashr z ys
  foldr-append ∅ z []       ys idl = sym (idl _)
  foldr-append ∅ z (x ∷ xs) ys idl rewrite assoc x (smashr ∅ xs) (smashr z ys)
                                         | foldr-append ∅ z xs ys idl
                                   = refl

  foldl-plus : ∀ z₁ z₂ xs → smashl (z₁ ∙ z₂) xs ≡ z₁ ∙ smashl z₂ xs
  foldl-plus z₁ z₂ []       = refl
  foldl-plus z₁ z₂ (x ∷ xs) rewrite assoc z₁ z₂ x
                            = foldl-plus _ _ xs

  foldr=foldl : ∀ ∅ → (∀ x → ∅ ∙ x ≡ x ∙ ∅) →
                ∀ xs → foldr _∙_ ∅ xs ≡ foldl _∙_ ∅ xs
  foldr=foldl ∅ id []       = refl
  foldr=foldl ∅ id (x ∷ xs) rewrite id x
                                  | foldl-plus x ∅ xs
                                  | foldr=foldl ∅ id xs
                            = refl

foldr-compose : ∀ {A B C : Set} (f : B → C → C) (z : C) (g : A → B) (xs : List A) →
                foldr (f ∘ g) z xs ≡ foldr f z (map g xs)
foldr-compose f z g []       = refl
foldr-compose f z g (x ∷ xs) rewrite foldr-compose f z g xs = refl

foldr-fusion : ∀ {A B C : Set} (f : B → C) (_⊕_ : A → B → B) (_⊗_ : A → C → C) (z : B) →
               (∀ x y → f (x ⊕ y) ≡ x ⊗ f y) →
               ∀ xs → f (foldr _⊕_ z xs) ≡ foldr _⊗_ (f z) xs
foldr-fusion f _⊕_ _⊗_ z distr []       = refl
foldr-fusion f _⊕_ _⊗_ z distr (x ∷ xs)
  rewrite sym (foldr-fusion f _⊕_ _⊗_ z distr xs)
  with    foldr _⊕_ z xs
...  |    y = distr x y
