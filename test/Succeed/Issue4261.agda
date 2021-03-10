{-# OPTIONS --allow-unsolved-metas #-}

record Sg (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

app : {A : Set} {B : A → Set} → ((x' : A) → B x') → (x : A) → B x
app f x = f x

ppa : {A : Set} {B : A → Set} → (x : A) → ((x' : A) → B x') → B x
ppa x f = f x

postulate
  Bool : Set
  bar : ((Sg Bool (λ _ → Bool)) → Bool) → Bool

foo : Bool
-- foo = app bar (λ (_ , _) → {!!}) -- accepted
foo = ppa (λ (_ , _) → {!!}) bar -- rejected
