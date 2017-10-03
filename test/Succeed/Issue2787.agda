
open import Agda.Builtin.Nat

data List (A : Set) : Set where
  lnil : List A
  lcons : A → List A → List A

data Vec (A : Set) : Nat → Set where
  vnil  : Vec A 0
  vcons : ∀ {n} → A → Vec A n → Vec A (suc n)

pattern [] = lnil
pattern [] = vnil

pattern _∷_ x xs = lcons x xs
pattern _∷_ y ys = vcons y ys

lmap : ∀ {A B} → (A → B) → List A → List B
lmap f [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

vmap : ∀ {A B n} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs
