
module _ where

module M where
  private
    module _ (A : Set) where
      Id : Set
      Id = A

  foo : Set → Set
  foo A = Id A

open M

bar : Set → Set
bar A = Id A -- Id should not be in scope
