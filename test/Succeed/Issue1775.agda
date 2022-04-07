{-# OPTIONS --cubical-compatible #-}

data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

infixr 5 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infix 4 _[_]=_

data _[_]=_ {a} {A : Set a} :
            {n : ℕ} → Vec A n → Fin n → A → Set a where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

Subset : ℕ → Set
Subset = Vec Bool

infix 4 _∈_

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= true

drop-there : ∀ {s n x} {p : Subset n} → suc x ∈ s ∷ p → x ∈ p
drop-there (there x∈p) = x∈p

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

data ⊥ : Set where

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

infix 4 _∈?_

_∈?_ : ∀ {n} x (p : Subset n) → Dec (x ∈ p)
zero  ∈? true  ∷ p = yes here
zero  ∈? false ∷ p = no  λ()
suc n ∈? s ∷ p       with n ∈? p
...                  | yes n∈p = yes (there n∈p)
...                  | no  n∉p = no  (n∉p ∘ drop-there)
