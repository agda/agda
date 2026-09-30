module Issue2447.Operator-error where

import Issue2447.M

_+_ : Set → Set → Set
A + _ = A

F : Set → Set
F A = A + A + A
