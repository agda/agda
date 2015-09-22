module WrongNamedArgument where

postulate
  f : {A : Set₁} → A → A

test : Set → Set
test = f {B = Set}

-- Good error:

-- Function does not accept argument {B = _}
-- when checking that {B = Set} are valid arguments to a function of
-- type {A : Set₁} → A → A
