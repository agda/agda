test : _
test = {!  !}
  where postulate
  Σ : (A : Set) (B : A → Set) → Set
  fst : (A : Set) (B : A → Set) → Σ A B → A
  case : (A B : Set) → A → (A → B) → B
