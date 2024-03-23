-- Tests termination of a function that has a stack of applications above
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.AppliedFunction where
data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

data Prod (A B : Set) : Set where
  prod : A → B → Prod A B

map1 : ∀ {A B C : Set} → (A → B) → Prod A C → Prod B C
map1 f (prod a b) = prod (f a) b

map2 : ∀ {A B C : Set} → (B → C) → Prod A B → Prod A C
map2 f (prod a b) = prod a (f b)


partitionᵇ : ∀ {A : Set} → (A → Bool) → List A → Prod (List A) (List A)
partitionᵇ p nil       = (prod nil nil)
partitionᵇ p (cons x xs) = (if p x then map1 else map2) (cons x) (partitionᵇ p xs)
