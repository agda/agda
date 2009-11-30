------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data Vec (a : Set) : ℕ → Set where
  []  : Vec a zero
  _∷_ : ∀ {n} (x : a) (xs : Vec a n) → Vec a (suc n)

infix 4 _∈_ _[_]=_

data _∈_ {a : Set} : a → {n : ℕ} → Vec a n → Set where
  here  : ∀ {n} {x}   {xs : Vec a n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : Vec a n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs

data _[_]=_ {a : Set} : {n : ℕ} → Vec a n → Fin n → a → Set where
  here  : ∀ {n}     {x}   {xs : Vec a n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec a n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

------------------------------------------------------------------------
-- Some operations

head : ∀ {a n} → Vec a (1 + n) → a
head (x ∷ xs) = x

tail : ∀ {a n} → Vec a (1 + n) → Vec a n
tail (x ∷ xs) = xs

[_] : ∀ {a} → a → Vec a 1
[ x ] = x ∷ []

infixr 5 _++_

_++_ : ∀ {a m n} → Vec a m → Vec a n → Vec a (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b n} → (a → b) → Vec a n → Vec b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

zipWith :  ∀ {a b c n}
        → (a → b → c) → Vec a n → Vec b n → Vec c n
zipWith _⊕_ []       []       = []
zipWith _⊕_ (x ∷ xs) (y ∷ ys) = (x ⊕ y) ∷ zipWith _⊕_ xs ys

zip : ∀ {a b n} → Vec a n → Vec b n → Vec (a × b) n
zip = zipWith _,_

replicate : ∀ {a n} → a → Vec a n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

foldr :  ∀ {a} (b : ℕ → Set) {m}
      → (∀ {n} → a → b n → b (suc n))
      → b zero
      → Vec a m → b m
foldr b _⊕_ n []       = n
foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ :  ∀ {a : Set} {m}
       → (a → a → a) → Vec a (suc m) → a
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl :  ∀ {a : Set} (b : ℕ → Set) {m}
      → (∀ {n} → b n → a → b (suc n))
      → b zero
      → Vec a m → b m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ :  ∀ {a : Set} {m}
       → (a → a → a) → Vec a (suc m) → a
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

concat : ∀ {a m n} → Vec (Vec a m) n → Vec a (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

splitAt : ∀ {A} m {n} (xs : Vec A (m + n)) →
          ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = ([] , xs , refl)
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | (ys , zs , refl) =
  ((x ∷ ys) , zs , refl)

take : ∀ {A} m {n} → Vec A (m + n) → Vec A m
take m xs          with splitAt m xs
take m .(ys ++ zs) | (ys , zs , refl) = ys

drop : ∀ {A} m {n} → Vec A (m + n) → Vec A n
drop m xs          with splitAt m xs
drop m .(ys ++ zs) | (ys , zs , refl) = zs

group : ∀ {A} n k (xs : Vec A (n * k)) →
        ∃ λ (xss : Vec (Vec A k) n) → xs ≡ concat xss
group zero    k []                  = ([] , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
  ((ys ∷ zss) , refl)

reverse : ∀ {a n} → Vec a n → Vec a n
reverse {a} = foldl (Vec a) (λ rev x → x ∷ rev) []

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _ _+_ 0

toList : ∀ {a n} → Vec a n → List a
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : ∀ {a} → (xs : List a) → Vec a (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a n} → Vec a n → a → Vec a (1 + n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

initLast : ∀ {A n} (xs : Vec A (1 + n)) →
           ∃₂ λ (ys : Vec A n) (y : A) → xs ≡ ys ∷ʳ y
initLast {n = zero}  (x ∷ [])         = ([] , x , refl)
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | (ys , y , refl) =
  ((x ∷ ys) , y , refl)

init : ∀ {A n} → Vec A (1 + n) → Vec A n
init xs         with initLast xs
init .(ys ∷ʳ y) | (ys , y , refl) = ys

last : ∀ {A n} → Vec A (1 + n) → A
last xs         with initLast xs
last .(ys ∷ʳ y) | (ys , y , refl) = y

infixl 1 _>>=_

_>>=_ : ∀ {A B m n} → Vec A m → (A → Vec B n) → Vec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛_

_⊛_ : ∀ {A B m n} → Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛ xs = fs >>= λ f → map f xs

-- Interleaves the two vectors.

infixr 5 _⋎_

_⋎_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

lookup : ∀ {a n} → Fin n → Vec a n → a
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

-- Update.

infixl 6 _[_]≔_

_[_]≔_ : ∀ {A n} → Vec A n → Fin n → A → Vec A n
[]       [ ()    ]≔ y
(x ∷ xs) [ zero  ]≔ y = y ∷ xs
(x ∷ xs) [ suc i ]≔ y = x ∷ xs [ i ]≔ y

-- Generates a vector containing all elements in Fin n. This function
-- is not placed in Data.Fin since Data.Vec depends on Data.Fin.

allFin : ∀ n → Vec (Fin n) n
allFin zero    = []
allFin (suc n) = zero ∷ map suc (allFin n)
