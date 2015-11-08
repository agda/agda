-- Andreas, 2012-03-30
module Issue593 where

import Common.Level
open import Common.Equality
open import Common.Irrelevance

record Unit : Set where
  constructor unit

bla6 : (F : Unit -> Set) ->
  let X : Unit -> Unit -> Set
      X = _
  in (z : Unit) -> X z z ≡ F z
bla6 F z = refl
-- non-linearity for singleton types should not matter

bla7 : (F : Unit -> Set) ->
  let X : Set
      X = _
  in (z : Unit) -> X ≡ F z
bla7 F z = refl
-- should eta expand z to unit

-- * a more involved singleton type:

record R (A : Set) : Set where
  constructor r
  field
    f1 : A -> Unit
    f2 : A

Sing : Set1
Sing = (A : Set) -> A -> R (A -> Unit)

test : (F : Sing -> Set) ->
  let X : Set
      X = _
  in (z : Sing) -> X ≡ F z
test F z = refl

-- * something with irrelevance

Sing' : Set1
Sing' = (A : Set) -> A -> R (Squash A)

test' : (F : Sing' -> Set) ->
  let X : Sing' -> Sing' -> Set
      X = _
  in (z : Sing') -> X z z ≡ F z
test' F z = refl
-- non-linearity should not matter
