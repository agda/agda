module _ where

module M where

  F : Set → Set
  F A = A

open M

infix 0 F
syntax F A = [ A ]

G : Set → Set
G A = [ A ]
