------------------------------------------------------------------------
-- Non-empty lists
------------------------------------------------------------------------

module Data.List.NonEmpty where

open import Data.Product hiding (map)
open import Data.Nat
open import Data.Function
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)
import Data.List as List
open List using (List; []; _∷_)
open import Category.Monad
open import Relation.Binary.PropositionalEquality

infixr 5 _∷_ _++_

data List⁺ (A : Set) : Set where
  [_] : (x : A) → List⁺ A
  _∷_ : (x : A) (xs : List⁺ A) → List⁺ A

length_-1 : ∀ {A} → List⁺ A → ℕ
length [ x ]  -1 = 0
length x ∷ xs -1 = 1 + length xs -1

------------------------------------------------------------------------
-- Conversion

fromVec : ∀ {n A} → Vec A (suc n) → List⁺ A
fromVec {zero}  (x ∷ []) = [ x ]
fromVec {suc n} (x ∷ xs) = x ∷ fromVec xs

toVec : ∀ {A} (xs : List⁺ A) → Vec A (suc (length xs -1))
toVec [ x ]    = Vec.[_] x
toVec (x ∷ xs) = x ∷ toVec xs

lift : ∀ {A B} →
       (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

fromList : ∀ {A} → A → List A → List⁺ A
fromList x xs = fromVec (Vec.fromList (x ∷ xs))

toList : ∀ {A} → List⁺ A → List A
toList = Vec.toList ∘ toVec

------------------------------------------------------------------------
-- Other operations

head : ∀ {A} → List⁺ A → A
head = Vec.head ∘ toVec

tail : ∀ {A} → List⁺ A → List A
tail = Vec.toList ∘ Vec.tail ∘ toVec

map : ∀ {A B} → (A → B) → List⁺ A → List⁺ B
map f = lift (λ xs → (, Vec.map f xs))

_++_ : ∀ {A} → List⁺ A → List⁺ A → List⁺ A
[ x ]    ++ ys = x ∷ ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {A} → List⁺ (List⁺ A) → List⁺ A
concat [ xs ]     = xs
concat (xs ∷ xss) = xs ++ concat xss

monad : RawMonad List⁺
monad = record
  { return = [_]
  ; _>>=_  = λ xs f → concat (map f xs)
  }

reverse : ∀ {A} → List⁺ A → List⁺ A
reverse = lift (,_ ∘′ Vec.reverse)

-- Note that s is only applied to the last element.

foldr : {A B : Set} → (A → B → B) → (A → B) → List⁺ A → B
foldr c s [ x ]    = s x
foldr c s (x ∷ xs) = c x (foldr c s xs)

-- Note that s is only applied to the first element.

foldl : {A B : Set} → (B → A → B) → (A → B) → List⁺ A → B
foldl c s [ x ]    = s x
foldl c s (x ∷ xs) = foldl c (c (s x)) xs

private
 module Examples {A B : Set}
                 (_⊕_ : A → B → B)
                 (_⊗_ : B → A → B)
                 (s : A → B)
                 (a b c : A)
                 where

  right : foldr _⊕_ s (a ∷ b ∷ [ c ]) ≡ a ⊕ (b ⊕ s c)
  right = refl

  left : foldl _⊗_ s (a ∷ b ∷ [ c ]) ≡ (s a ⊗ b) ⊗ c
  left = refl
