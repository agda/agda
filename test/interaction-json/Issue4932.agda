module Issue4932 where

data ⊤
  : Set
  where

  tt
    : ⊤

f
  : {A : Set}
  → {x : ⊤}
  → ⊤
f
  = ?

