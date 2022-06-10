-- Andreas, 2022-06-10
-- A failed attempt to break Prop ≤ Set.
-- See https://github.com/agda/agda/issues/5761#issuecomment-1151336715

{-# OPTIONS --prop --cumulativity #-}

data   ⊥ : Set where
record ⊤ : Set where
  constructor tt

data Fool : Prop where
  true false : Fool

Bool : Set
Bool = Fool

True : Bool → Set
True true  = ⊤
True false = ⊥

X : Fool → Set

true≡false : X true → X false
true≡false x = x

X = True

-- Now we have  True true → True false  which looks dangerous...
-- But we cannot exploit it:

fails : ⊥
fails = true≡false tt

-- ERROR:
-- ⊤ !=< (True _)
-- when checking that the expression tt has type X _
