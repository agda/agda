
open import Common.Prelude hiding (length; map)

pattern [_] x = x ∷ []
pattern tail {x} xs = x ∷ xs

length : ∀ {A : Set} → List A → Nat
length [] = 0
length [ _ ] = 1
length (tail [ _ ]) = 2
length (tail (tail xs)) = 2 + length xs

data Vec (A : Set) : Nat → Set where
  nil : Vec A 0
  cons : ∀ n → A → Vec A n → Vec A (suc n)

pattern _∷v_ {n} x xs = cons n x xs

map : ∀ {A B n} → (A → B) → Vec A n → Vec B n
map f nil = nil
map f (x ∷v xs) = f x ∷v map f xs

data SomeVec (A : Set) : Set where
  someVec : ∀ n → Vec A n → SomeVec A

pattern some {n} xs = someVec n xs

null : ∀ {A} → SomeVec A → Bool
null (some nil)      = true
null (some (_ ∷v _)) = false  -- check that the hidden arg can be instantiated to a dot pattern
