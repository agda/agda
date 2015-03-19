module _ where

module A where

  postulate
    _∷_ _∙_ bind : Set

  infixr 5 _∷_
  infixr 5 _∙_
  infix  1 bind

  syntax bind c (λ x → d) = x ← c , d

module B where

  postulate
    _∷_ _∙_ bind : Set

  infix  5 _∷_
  infixr 4 _∙_
  infixl 2 bind

  syntax bind c d = c ∙ d

module C where

  postulate
    bind : Set

  infixr 2 bind

  syntax bind c d = c ∙ d

open A
open B
open C

-- _∷_ is infix 5.
-- _∙_ has two fixities: infixr 4 and infixr 5.
-- A.bind's notation is infix 1.
-- B.bind and C.bind's notations are infix 2.

-- There is one instance of _∷_ in the grammar.

-- There are three instances of _∙_ in the grammar, one
-- corresponding to A._∙_, one corresponding to B._∙_, and one
-- corresponding to both B.bind and C.bind.

Foo : Set
Foo = ∷ ∙ ← ,
