-- Andreas, 2012-09-17
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.type:15 -v syntax.reify.con:30 #-}
module ReifyConstructorParametersForWith where

import Common.Level

module M {i} {I : Set i} where

  data D : Set i where
    c : {i : I} → D  -- danger of confusion for c {i = ...}

  data P : D → Set i where
    p : {x : I} → P (c {x})

  Pc : (x : I) → Set i
  Pc x = P (c {x})

  works : ∀ (x : I) → Pc x → Pc x
  works x y with Set
  ... | _ = y

  module N (x : I) where

    bla : Pc x → Pc x
    bla y with Set
    ... | _ = y

open M

test : ∀ {i}{I : Set i}(x : I) → Pc x → Pc x
test x y with Set
... | _ = y
-- If reification does not reify constructor parameters
-- for generating the with type, it confuses constructor
-- parameter {i} with constructor argument {i}.

