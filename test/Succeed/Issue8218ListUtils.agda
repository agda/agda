open import Agda.Builtin.List public
open import Agda.Builtin.Equality

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

postulate _++_ : ∀{A : Set} → List A → List A → List A

postulate
  map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
