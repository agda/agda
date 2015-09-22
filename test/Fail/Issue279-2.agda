module Issue279-2 where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

module M (A : Set) where

  data P : ⊤ → Set where
    tt : A → P tt

module X = M ⊥ using (tt)
open X

good : ⊥ → M.P ⊥ tt
good = tt

bad : M.P ⊤ tt
bad = tt tt
