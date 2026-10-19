
module _ where

postulate
  F : Set → Set
  A : Set

module A (X : Set) where
  postulate T : Set

module B where
  private module M = A A
  open M
  postulate t : F T

postulate
  op : {A : Set} → A → A → A

open A A

foo : F T
foo = op B.t {!!}   -- ?0 : F .ReduceNotInScope.B.M.T
