------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List)
open import Data.Product using (_×_; _,_)

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

infixr 5 _++'_

data SplitAt {a : Set} (m : ℕ) {n : ℕ} : Vec a (m + n) → Set where
  _++'_ : (xs : Vec a m) (ys : Vec a n) → SplitAt m (xs ++ ys)

splitAt : ∀ {a} m {n} (xs : Vec a (m + n)) → SplitAt m xs
splitAt zero    xs                = [] ++' xs
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | ys ++' zs = (x ∷ ys) ++' zs

take : ∀ {a} m {n} → Vec a (m + n) → Vec a m
take m xs with splitAt m xs
take m .(xs ++ ys) | xs ++' ys = xs

drop : ∀ {a} m {n} → Vec a (m + n) → Vec a n
drop m xs with splitAt m xs
drop m .(xs ++ ys) | xs ++' ys = ys

data Group {a : Set} (n k : ℕ) : Vec a (n * k) → Set where
  concat' : (xss : Vec (Vec a k) n) → Group n k (concat xss)

group : ∀ {a} n k (xs : Vec a (n * k)) → Group n k xs
group zero    k []                  = concat' []
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | ys ++' zs with group n k zs
group (suc n) k .(ys ++ concat zss) | ys ++' ._ | concat' zss = concat' (ys ∷ zss)

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

infixl 5 _∷ʳ'_

data InitLast {a : Set} (n : ℕ) : Vec a (1 + n) → Set where
  _∷ʳ'_ : (xs : Vec a n) (x : a) → InitLast n (xs ∷ʳ x)

initLast : ∀ {a n} (xs : Vec a (1 + n)) → InitLast n xs
initLast {n = zero}  (x ∷ [])         = [] ∷ʳ' x
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

init : ∀ {a n} → Vec a (1 + n) → Vec a n
init xs with initLast xs
init .(ys ∷ʳ y) | ys ∷ʳ' y = ys

last : ∀ {a n} → Vec a (1 + n) → a
last xs with initLast xs
last .(ys ∷ʳ y) | ys ∷ʳ' y = y

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
