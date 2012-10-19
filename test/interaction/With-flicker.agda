module With-flicker where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

fib : ℕ → ℕ
fib zero          = zero
fib (suc zero)    = suc zero
fib (suc (suc n)) = fib n + fib (suc n)

thirteen = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

postulate
  P : ℕ → Set
  n : ℕ

-- The interactive highlighting used to flicker a lot when the
-- following definition was checked.

Foo : P (fib (thirteen + n)) → Set₁
Foo p with zero
Foo p | _ = Set

-- TODO: Make sure that interactive highlighting output is included in
-- With-flicker.out.
