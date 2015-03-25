
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

app : {A B : Set} → (A → B) × A → B
app (f , x) = f x

data D : Set where d : D

postulate
  P   : {A : Set} → A → Set
  p   : (f : D → D) → P f → P (f d)
  foo : (F : Set → Set) → F D
  bar : (F : Set → Set) → P (foo F)

q : P (app (foo (λ A → (A → A) × A)))
q =
  let H : Set → Set
      H = _ in
  p (foo H) (bar H)

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:668
