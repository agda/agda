-- popular functions on lists are terminating
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Lists where


data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

map : ∀ {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

rev  : ∀ {A : Set} → List A → List A
rev1 : ∀ {A : Set} → List A → List A → List A

rev l = rev1 l nil

rev1 nil a = a
rev1 (cons x l) a = rev1 l (cons x a)

foldl : ∀ {A B : Set} → (A → B → A) → A → List B → A
foldl c n nil       = n
foldl c n (cons x xs) = foldl c (c n x) xs
