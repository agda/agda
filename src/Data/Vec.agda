------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

open import Category.Functor
open import Category.Applicative
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base as List using (List)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infix 4 _∈_

data _∈_ {a} {A : Set a} : A → {n : ℕ} → Vec A n → Set a where
  here  : ∀ {n} {x}   {xs : Vec A n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : Vec A n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs

infix 4 _[_]=_

data _[_]=_ {a} {A : Set a} :
            {n : ℕ} → Vec A n → Fin n → A → Set a where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

------------------------------------------------------------------------
-- Some operations

head : ∀ {a n} {A : Set a} → Vec A (1 + n) → A
head (x ∷ xs) = x

tail : ∀ {a n} {A : Set a} → Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs

[_] : ∀ {a} {A : Set a} → A → Vec A 1
[ x ] = x ∷ []

infixr 5 _++_

_++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixl 4 _⊛_

_⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ _        = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

replicate : ∀ {a n} {A : Set a} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

applicative : ∀ {a n} → RawApplicative (λ (A : Set a) → Vec A n)
applicative = record
  { pure = replicate
  ; _⊛_  = _⊛_
  }

map : ∀ {a b n} {A : Set a} {B : Set b} →
      (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

functor :  ∀ {a n} → RawFunctor (λ (A : Set a) → Vec A n)
functor = record
  { _<$>_ = map
  }

zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
          (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zip : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

unzip : ∀ {a b n} {A : Set a} {B : Set b} →
        Vec (A × B) n → Vec A n × Vec B n
unzip []              = [] , []
unzip ((x , y) ∷ xys) = Prod.map (x ∷_) (y ∷_) (unzip xys)

foldr : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → A → B n → B (suc n)) →
        B zero →
        Vec A m → B m
foldr b _⊕_ n []       = n
foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ : ∀ {a} {A : Set a} {m} →
         (A → A → A) → Vec A (suc m) → A
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ : ∀ {a} {A : Set a} {m} →
         (A → A → A) → Vec A (suc m) → A
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

concat : ∀ {a m n} {A : Set a} →
         Vec (Vec A m) n → Vec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

splitAt : ∀ {a} {A : Set a} m {n} (xs : Vec A (m + n)) →
          ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = ([] , xs , refl)
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | (ys , zs , refl) =
  ((x ∷ ys) , zs , refl)

take : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A m
take m xs          with splitAt m xs
take m .(ys ++ zs) | (ys , zs , refl) = ys

drop : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A n
drop m xs          with splitAt m xs
drop m .(ys ++ zs) | (ys , zs , refl) = zs

group : ∀ {a} {A : Set a} n k (xs : Vec A (n * k)) →
        ∃ λ (xss : Vec (Vec A k) n) → xs ≡ concat xss
group zero    k []                  = ([] , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
  ((ys ∷ zss) , refl)

-- Splits a vector into two "halves".

split : ∀ {a n} {A : Set a} → Vec A n → Vec A ⌈ n /2⌉ × Vec A ⌊ n /2⌋
split []           = ([]     , [])
split (x ∷ [])     = (x ∷ [] , [])
split (x ∷ y ∷ xs) = Prod.map (_∷_ x) (_∷_ y) (split xs)

reverse : ∀ {a n} {A : Set a} → Vec A n → Vec A n
reverse {A = A} = foldl (Vec A) (λ rev x → x ∷ rev) []

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _ _+_ 0

toList : ∀ {a n} {A : Set a} → Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : ∀ {a} {A : Set a} → (xs : List A) → Vec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a n} {A : Set a} → Vec A n → A → Vec A (1 + n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

initLast : ∀ {a n} {A : Set a} (xs : Vec A (1 + n)) →
           ∃₂ λ (ys : Vec A n) (y : A) → xs ≡ ys ∷ʳ y
initLast {n = zero}  (x ∷ [])         = ([] , x , refl)
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | (ys , y , refl) =
  ((x ∷ ys) , y , refl)

init : ∀ {a n} {A : Set a} → Vec A (1 + n) → Vec A n
init xs         with initLast xs
init .(ys ∷ʳ y) | (ys , y , refl) = ys

last : ∀ {a n} {A : Set a} → Vec A (1 + n) → A
last xs         with initLast xs
last .(ys ∷ʳ y) | (ys , y , refl) = y

-- Multiplying vectors

infixl 1 _>>=_

_>>=_ : ∀ {a b m n} {A : Set a} {B : Set b} →
        Vec A m → (A → Vec B n) → Vec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : ∀ {a b m n} {A : Set a} {B : Set b} →
       Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛* xs = fs >>= λ f → map f xs

allPairs : ∀ {a b} {A : Set a} {B : Set b} {m n}
           → Vec A m → Vec B n → Vec (A × B) (m * n)
allPairs xs ys = map _,_ xs ⊛* ys

-- Interleaves the two vectors.

infixr 5 _⋎_

_⋎_ : ∀ {a m n} {A : Set a} →
      Vec A m → Vec A n → Vec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- A lookup function.

lookup : ∀ {a n} {A : Set a} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

-- An inverse of flip lookup.

tabulate : ∀ {n a} {A : Set a} → (Fin n → A) → Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

-- Update.

infixl 6 _[_]≔_

_[_]≔_ : ∀ {a n} {A : Set a} → Vec A n → Fin n → A → Vec A n
(x ∷ xs) [ zero  ]≔ y = y ∷ xs
(x ∷ xs) [ suc i ]≔ y = x ∷ xs [ i ]≔ y

-- Generates a vector containing all elements in Fin n. This function
-- is not placed in Data.Fin because Data.Vec depends on Data.Fin.
--
-- The implementation was suggested by Conor McBride ("Fwd: how to
-- count 0..n-1", http://thread.gmane.org/gmane.comp.lang.agda/2554).

allFin : ∀ n → Vec (Fin n) n
allFin _ = tabulate id
