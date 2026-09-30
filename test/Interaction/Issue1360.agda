-- {-# OPTIONS -v interaction.give:20 #-}

-- Reported by stevan.andjelkovic, Yesterday (17 hours ago)

-- Trying to give the expression in the goal gives the following error:

--   tt != tt p a of type Prop
--   when checking that the expression (λ x y → ?) has type
--   ({o : ⊤} (p : ⊤) → ⊥ → ⊤)


record _▷_ (I O : Set) : Set₁ where
  constructor _◃_/_
  field
    Parameter  : (o : O) → Set
    Arity      : ∀ {o} (p : Parameter o) → Set
    input      : ∀ {o} (p : Parameter o) (a : Arity p) → I

open _▷_ public

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

--data ⊤ : Set where
--  tt : ⊤

Abort : ⊤ ▷ ⊤
Abort = (λ _ → ⊤) ◃ (λ _ → ⊥) / {!!λ x y → {!!}!}
