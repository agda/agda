-- Andreas, 2014-05-03 Test case by Andrea Vezzosi

data Two : Set where
  a b : Two

-- This example of varying arity crashed Epic before.
f : Two → {eq : Two} → Two
f a   {x} = a
f b       = b

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}

postulate
  return  : ∀ {A} → A → IO A

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}

main : IO Two
main = return a
