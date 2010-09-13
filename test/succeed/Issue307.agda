module Issue307 where

postulate A : Set

_! : A → A
x ! = x

! : A → A
! x = x


data D : Set where
  d : D → D

syntax d x = x d

f : D → D
f (x d) = x

g : D → D
g (d x) = x



