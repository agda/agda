postulate ANY  : ∀ {a} {A : Set a} → A

variable A : Set _

F : ∀ {l} (A : Set l) (a : A) → Set

postulate
  f   : ∀ {l} (A : Set l) (a : A) → F A a
  g   : (a : A) → F A a → Set
  g-f : (a : A) → g _ (f A a)

F A = ANY
