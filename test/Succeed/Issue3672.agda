{-# OPTIONS --allow-unsolved-metas #-}

data C (A : Set) : Set where
  c : (x : A) → C A

data D : Set where

data E (A : Set) : Set where
  e : A → E A

postulate
  F : {A : Set} → A → Set

G : {A : Set} → C A → Set
G (c x) = E (F x)

postulate
  H : {A : Set} → (A → Set) → C A → Set
  f : {A : Set} {P : A → Set} {y : C A} → H P y → (x : A) → G y → P x
  g : {A : Set} {y : C A} {P : A → Set} → ((x : A) → G y → P x) → H P y

variable
  A : Set
  P : A → Set
  x : A
  y : C A

postulate
  h : {p : ∀ x → G y → P x} → (∀ x (g : G y) → F (p x g)) → F (g p)

id : (A : Set) → A → A
id _ x = x

-- i : (h : H P y) → (∀ x (g : G y) → F (f h x g)) → F (g (f h))
-- i x y = id (F (g (f x))) (h y)
