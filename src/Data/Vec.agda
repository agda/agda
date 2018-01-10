------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

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
-- Basic operations

head : ∀ {a n} {A : Set a} → Vec A (1 + n) → A
head (x ∷ xs) = x

tail : ∀ {a n} {A : Set a} → Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs

lookup : ∀ {a n} {A : Set a} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

-- Update.

infixl 6 _[_]≔_

_[_]≔_ : ∀ {a n} {A : Set a} → Vec A n → Fin n → A → Vec A n
(x ∷ xs) [ zero  ]≔ y = y ∷ xs
(x ∷ xs) [ suc i ]≔ y = x ∷ xs [ i ]≔ y

------------------------------------------------------------------------
-- Operations for transforming vectors

map : ∀ {a b n} {A : Set a} {B : Set b} →
      (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Concatenation.

infixr 5 _++_

_++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {a m n} {A : Set a} →
         Vec (Vec A m) n → Vec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

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

-- Interleaving.

infixr 5 _⋎_

_⋎_ : ∀ {a m n} {A : Set a} →
      Vec A m → Vec A n → Vec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- Pointwise application

infixl 4 _⊛_

_⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ _        = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

-- Multiplication

infixl 1 _>>=_

_>>=_ : ∀ {a b m n} {A : Set a} {B : Set b} →
        Vec A m → (A → Vec B n) → Vec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : ∀ {a b m n} {A : Set a} {B : Set b} →
       Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛* xs = fs >>= λ f → map f xs

allPairs : ∀ {a b m n} {A : Set a} {B : Set b} →
           Vec A m → Vec B n → Vec (A × B) (m * n)
allPairs xs ys = map _,_ xs ⊛* ys

------------------------------------------------------------------------
-- Operations for reducing vectors

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

-- Special folds

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _ _+_ 0

------------------------------------------------------------------------
-- Operations for building vectors

[_] : ∀ {a} {A : Set a} → A → Vec A 1
[ x ] = x ∷ []

replicate : ∀ {a n} {A : Set a} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

tabulate : ∀ {n a} {A : Set a} → (Fin n → A) → Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

allFin : ∀ n → Vec (Fin n) n
allFin _ = tabulate id

------------------------------------------------------------------------
-- Operations for dividing vectors

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

split : ∀ {a n} {A : Set a} → Vec A n → Vec A ⌈ n /2⌉ × Vec A ⌊ n /2⌋
split []           = ([]     , [])
split (x ∷ [])     = (x ∷ [] , [])
split (x ∷ y ∷ xs) = Prod.map (_∷_ x) (_∷_ y) (split xs)

------------------------------------------------------------------------
-- Operations for converting between lists

toList : ∀ {a n} {A : Set a} → Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : ∀ {a} {A : Set a} → (xs : List A) → Vec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

------------------------------------------------------------------------
-- Operations for reversing vectors

reverse : ∀ {a n} {A : Set a} → Vec A n → Vec A n
reverse {A = A} = foldl (Vec A) (λ rev x → x ∷ rev) []

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
