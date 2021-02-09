
abstract

  data D : Set where
    d : D

  data P : D → Set where
    p : P d

  d′ : D
  d′ = d

  d₂ : D
  d₂ = d

private
  abstract
    p′ : P d
    p′ = p

A : P d′
A = p′

-- A : Set₁ -- P d′
-- A = Set -- p′
--   where

--   abstract

--     p′ : P d
--     p′ = p
