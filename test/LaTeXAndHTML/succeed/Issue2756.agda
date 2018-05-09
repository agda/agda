module Issue2756 where

module M where

  postulate A : Set

module M′ = M

B : Set
B = M′.A
