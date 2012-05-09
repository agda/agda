
module Issue628 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

0≢1+n : ∀ {n} -> 0 ≡ suc n → ⊥
0≢1+n ()

divSucAux : (k m n j : ℕ) -> ℕ
divSucAux k m zero j = k
divSucAux k m (suc n) zero = divSucAux (suc k) m n m
divSucAux k m (suc n) (suc j) = divSucAux k m n j
{-# BUILTIN NATDIVSUCAUX divSucAux #-}

oh-noes : ⊥
oh-noes = 0≢1+n {divSucAux 0 0 0 1} refl
