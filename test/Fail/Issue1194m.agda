module _ where

postulate D : Set

module A where

  infixr 5 _∷_

  postulate
    _∷_ : Set₁ → D → D

module B where

  infix 5 _∷_

  postulate
    _∷_ : Set₁ → Set₁ → D

open A
open B

foo : D
foo = Set ∷ Set

-- Expected error:
--
-- <preciseErrorLocation>
-- Ambiguous name _∷_. It could refer to any one of
--   A._∷_ bound at ...
--   B._∷_ bound at ...
