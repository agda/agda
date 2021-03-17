-- Duplicate of #1984

postulate
  Path : {A : Set} → A → Set
  admit : {Z : Set} → Z
  X : Set
  Y : X → Set
  Y' : X → Set

record Square : Set₁ where
  field
    A : Set
    B : Set
    b : B
    coh : Path b

-- Spurious mutual block to trigger the problem
mut : Set

record Cocone : Set where
  field
    x : X

-- x : Cocone → X
-- x (mkCocone x) = x

postulate
  m n : Cocone
  fung : (c : Cocone) → Y' (Cocone.x c) → Path c

record CoconeDep (P : X → Set) : Set where
  inductive
  field
    x' : P (Cocone.x m)

s : Square
s .Square.A = CoconeDep Y
s .Square.B = Cocone
s .Square.b = n
s .Square.coh = fung _ (admit {Y' (Cocone.x (s .Square.b))})

mut = X
