
module _ where

module M (X : Set) where
  postulate
    F : Set
    G : Set

data ⊥ : Set where

open M ⊥ hiding (F)

easy : M.G ⊥
easy = {!!}   -- G

hard : M.F ⊥
hard = {!!}    -- M.F ⊥ (and not .Issue1640._.F)

data ⊤ : Set where
  tt : ⊤

module With where
  private
    F : ⊤ → Set
    F x with x
    F _ | tt = ⊥

  T = F

tricky : ∀ t → With.T t
tricky t = {!!}  -- .Issue1640.With.F t | t
