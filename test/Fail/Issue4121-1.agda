module _ where

module M where

  data D : Set where
    c : D

  private

    pattern c′ = c

open M

x : D
x = c′
