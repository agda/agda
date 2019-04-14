{-# OPTIONS --cubical #-}
module _ where
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data Interval : Set where
  left right : Interval
  sq      : left ≡ right


-- Agda should not loop when typechecking the following definition.
--
-- Termination checking should catch that `id left` is not
-- normalizing, given our definition of reduction.
--
-- Hence conversion checking shouldn't reduce applications of `id`.
id : Interval → Interval
id (sq i) = sq i
id left = id (sq i0)
id right = id (sq i1)
