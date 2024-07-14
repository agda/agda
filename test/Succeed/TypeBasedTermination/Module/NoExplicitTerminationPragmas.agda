module TypeBasedTermination.Module.NoExplicitTerminationPragmas where

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

map : ∀ {A B} → (A → B) → List A → List B
map f nil         = nil
map f (cons a as) = cons (f a) (map f as)

data Rose (A : Set) : Set where
  rose : A → List (Rose A) → Rose A
