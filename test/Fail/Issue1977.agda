module _ where

module M where

  postulate
    [_] : Set → Set

Foo = [ M.undefined ]
