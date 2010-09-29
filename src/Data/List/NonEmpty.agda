------------------------------------------------------------------------
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}
module Data.List.NonEmpty where

open import Data.Product hiding (map)
open import Data.Nat
open import Function
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Category.Monad
open import Relation.Binary.PropositionalEquality

infixr 5 _∷_ _∷ʳ_ _⁺++⁺_ _++⁺_ _⁺++_

data List⁺ {ℓ} (A : Set ℓ) : Set ℓ where
  [_] : (x : A) → List⁺ A
  _∷_ : (x : A) (xs : List⁺ A) → List⁺ A

length_-1 : ∀ {ℓ} {A : Set ℓ} → List⁺ A → ℕ
length [ x ]  -1 = 0
length x ∷ xs -1 = 1 + length xs -1

------------------------------------------------------------------------
-- Conversion

fromVec : ∀ {ℓ n} {A : Set ℓ} → Vec A (suc n) → List⁺ A
fromVec {_} {zero}  (x ∷ _)  = [ x ]
fromVec {_} {suc n} (x ∷ xs) = x ∷ fromVec xs

toVec : ∀ {ℓ} {A : Set ℓ} (xs : List⁺ A) → Vec A (suc (length xs -1))
toVec [ x ]    = Vec.[_] x
toVec (x ∷ xs) = x ∷ toVec xs

lift : ∀ {ℓ} {A B : Set ℓ} →
       (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

fromList : ∀ {ℓ} {A : Set ℓ} → A → List A → List⁺ A
fromList x xs = fromVec (Vec.fromList (x ∷ xs))

toList : ∀ {ℓ} {A : Set ℓ} → List⁺ A → List A
toList {ℓ} = Vec.toList {ℓ} ∘ toVec

------------------------------------------------------------------------
-- Other operations

head : ∀ {ℓ} {A : Set ℓ} → List⁺ A → A
head {ℓ} = Vec.head {ℓ} ∘ toVec

tail : ∀ {ℓ} {A : Set ℓ} → List⁺ A → List A
tail {ℓ} = Vec.toList {ℓ} ∘ Vec.tail {ℓ} ∘ toVec

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → List⁺ A → List⁺ B
map f = lift (λ xs → (, Vec.map f xs))

-- Right fold. Note that s is only applied to the last element (see
-- the examples below).

foldr : ∀ {ℓ} {A B : Set ℓ} → (A → B → B) → (A → B) → List⁺ A → B
foldr c s [ x ]    = s x
foldr c s (x ∷ xs) = c x (foldr c s xs)

-- Left fold. Note that s is only applied to the first element (see
-- the examples below).

foldl : ∀ {ℓ} {A B : Set ℓ} → (B → A → B) → (A → B) → List⁺ A → B
foldl c s [ x ]    = s x
foldl c s (x ∷ xs) = foldl c (c (s x)) xs

-- Append (several variants).

_⁺++⁺_ : ∀ {ℓ} {A : Set ℓ} → List⁺ A → List⁺ A → List⁺ A
xs ⁺++⁺ ys = foldr _∷_ (λ x → x ∷ ys) xs

_⁺++_ : ∀ {ℓ} {A : Set ℓ} → List⁺ A → List A → List⁺ A
xs ⁺++ ys = foldr _∷_ (λ x → fromList x ys) xs

_++⁺_ : ∀ {ℓ} {A : Set ℓ} → List A → List⁺ A → List⁺ A
xs ++⁺ ys = List.foldr _∷_ ys xs

concat : ∀ {ℓ} {A : Set ℓ} → List⁺ (List⁺ A) → List⁺ A
concat [ xs ]     = xs
concat (xs ∷ xss) = xs ⁺++⁺ concat xss

monad : RawMonad List⁺
monad = record
  { return = [_]
  ; _>>=_  = λ xs f → concat (map f xs)
  }

reverse : ∀ {ℓ} {A : Set ℓ} → List⁺ A → List⁺ A
reverse = lift (,_ ∘′ Vec.reverse)

-- Snoc.

_∷ʳ_ : ∀ {ℓ} {A : Set ℓ} → List⁺ A → A → List⁺ A
xs ∷ʳ x = foldr _∷_ (λ y → y ∷ [ x ]) xs

-- A snoc-view of non-empty lists.

infixl 5 _∷ʳ′_

data SnocView {ℓ} {A : Set ℓ} : List⁺ A → Set ℓ where
  [_]   : (x : A)                → SnocView [ x ]
  _∷ʳ′_ : (xs : List⁺ A) (x : A) → SnocView (xs ∷ʳ x)

snocView : ∀ {ℓ} {A : Set ℓ} (xs : List⁺ A) → SnocView xs
snocView [ x ]            = [ x ]
snocView (x ∷ xs)         with snocView xs
snocView (x ∷ .([ y ]))   | [ y ]    = [ x ] ∷ʳ′ y
snocView (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ′ y = (x ∷ ys) ∷ʳ′ y

-- The last element in the list.

last : ∀ {ℓ} {A : Set ℓ} → List⁺ A → A
last xs with snocView xs
last .([ y ])   | [ y ]    = y
last .(ys ∷ʳ y) | ys ∷ʳ′ y = y

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
 module Examples {A B : Set}
                 (_⊕_ : A → B → B)
                 (_⊗_ : B → A → B)
                 (f : A → B)
                 (a b c : A)
                 where

  hd : head (a ∷ b ∷ [ c ]) ≡ a
  hd = refl

  tl : tail (a ∷ b ∷ [ c ]) ≡ b ∷ c ∷ []
  tl = refl

  mp : map f (a ∷ b ∷ [ c ]) ≡ f a ∷ f b ∷ [ f c ]
  mp = refl

  right : foldr _⊕_ f (a ∷ b ∷ [ c ]) ≡ a ⊕ (b ⊕ f c)
  right = refl

  left : foldl _⊗_ f (a ∷ b ∷ [ c ]) ≡ (f a ⊗ b) ⊗ c
  left = refl

  ⁺app⁺ : (a ∷ b ∷ [ c ]) ⁺++⁺ (b ∷ [ c ]) ≡
          a ∷ b ∷ c ∷ b ∷ [ c ]
  ⁺app⁺ = refl

  ⁺app : (a ∷ b ∷ [ c ]) ⁺++ (b ∷ c ∷ []) ≡
          a ∷ b ∷ c ∷ b ∷ [ c ]
  ⁺app = refl

  app⁺ : (a ∷ b ∷ c ∷ []) ++⁺ (b ∷ [ c ]) ≡
          a ∷ b ∷ c ∷ b ∷ [ c ]
  app⁺ = refl

  conc : concat ((a ∷ b ∷ [ c ]) ∷ [ b ∷ [ c ] ]) ≡
         a ∷ b ∷ c ∷ b ∷ [ c ]
  conc = refl

  rev : reverse (a ∷ b ∷ [ c ]) ≡ c ∷ b ∷ [ a ]
  rev = refl

  snoc : (a ∷ b ∷ [ c ]) ∷ʳ a ≡ a ∷ b ∷ c ∷ [ a ]
  snoc = refl
