-- 2014-05-02
-- This looped in the epic backend after Andreas' big projection refactoring (Oct 2013)

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}   -- Essential

f : ℕ → ℕ
f zero    = zero
f (suc m) = m

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}

postulate
  return  : ∀ {A} → A → IO A

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}

main : IO ℕ
main = return zero

