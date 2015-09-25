
module Issue279 where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

module M (A : Set) where

  data P : ⊤ → Set where
    tt : A → P tt

open M ⊥ using (tt)

good : ⊥ → M.P ⊥ tt
good = tt

bad : M.P ⊤ tt
bad = tt tt
