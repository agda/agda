open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] ys = ys
reverseAcc (x ∷ xs) ys = reverseAcc xs (x ∷ ys)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

data Vec (A : Set) : Nat → Set where
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

postulate
  replicate : ∀ {A : Set} {n} → A → Vec A n
  zipWith : ∀ {A B C : Set} {n} → (A → B → C) → Vec A n → Vec B n → Vec C n

macro
  rtest : Name → Term → TC ⊤
  rtest f a = do
     (function (clause tel _ t ∷ [])) ← withReconstructed (getDefinition f) where
        _ → typeError (strErr "ERROR" ∷ [])
     t ← inContext (reverse tel) (normalise t)
     quoteTC t >>= unify a

transp : ∀ m n → Vec (Vec Nat n) m → Vec (Vec Nat m) n
transp .(suc m) n (_∷_ {m} x xs) = zipWith {Nat} {Vec Nat m} {Vec Nat (suc m)} {n} (_∷_ {Nat} {m}) x (transp _ n xs)

test : Term
test = rtest transp
