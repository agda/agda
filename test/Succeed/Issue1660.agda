{-# OPTIONS --rewriting --confluence-check #-}

postulate
  _↦_ : {A : Set} → A → A → Set
  idr : {A : Set} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B


postulate
  A B C : Set
  g : A → B → C

f : A × B → C
f (x , y) = g x y


postulate
  D : Set
  P : (A → B → C) → D
  res : D
  rew : P (λ x y → g x y) ↦ res
  {-# REWRITE rew #-}

test : P (λ x y → f (x , y)) ↦ res
test = idr
