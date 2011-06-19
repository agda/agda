{-# OPTIONS --universe-polymorphism #-}
module UniversePolymorphism where

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level
  max : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsuc #-}
{-# BUILTIN LEVELMAX max #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

infixr 40 _∷_

data Vec {i}(A : Set i) : Nat → Set i where
  []  : Vec {i} A zero
  _∷_ : ∀ {n} → A → Vec {i} A n → Vec {i} A (suc n)

map : ∀ {n a b}{A : Set a}{B : Set b} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

vec : ∀ {n a}{A : Set a} → A → Vec A n
vec {zero}  _ = []
vec {suc n} x = x ∷ vec x

_<*>_ : ∀ {n a b}{A : Set a}{B : Set b} → Vec (A → B) n → Vec A n → Vec B n
[]       <*> []       = []
(f ∷ fs) <*> (x ∷ xs) = f x ∷ (fs <*> xs)

flip : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} →
       (A → B → C) → B → A → C
flip f x y = f y x

module Zip where

  Fun : ∀ {n a} → Vec (Set a) n → Set a → Set a
  Fun []       B = B
  Fun (A ∷ As) B = A → Fun As B

  app : ∀ {n m a}(As : Vec (Set a) n)(B : Set a) →
        Vec (Fun As B) m → Fun (map (flip Vec m) As) (Vec B m)
  app []       B bs = bs
  app (A ∷ As) B fs = λ as → app As B (fs <*> as) 

  zipWith : ∀ {n m a}(As : Vec (Set a) n)(B : Set a) →
            Fun As B → Fun (map (flip Vec m) As) (Vec B m)
  zipWith As B f = app As B (vec f)

  zipWith₃ : ∀ {n a}{A B C D : Set a} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n
  zipWith₃ = zipWith (_ ∷ _ ∷ _ ∷ []) _

data Σ {a b}(A : Set a)(B : A → Set b) : Set (max a b) where
  _,_ : (x : A)(y : B x) → Σ A B

fst : ∀ {a b}{A : Set a}{B : A → Set b} → Σ A B → A
fst (x , y) = x

snd : ∀ {a b}{A : Set a}{B : A → Set b}(p : Σ A B) → B (fst p)
snd (x , y) = y

-- Normal Σ
List : ∀ {a} → Set a → Set a
List A = Σ _ (Vec A)

nil : ∀ {a}{A : Set a} → List A
nil = _ , []

cons : ∀ {a}{A : Set a} → A → List A → List A
cons x (_ , xs) = _ , x ∷ xs

AnyList : ∀ {i} → Set (lsuc i)
AnyList {i} = Σ (Set i) (List {i})
