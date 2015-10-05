-- Andreas, 2015-10-05, issue reported by mechvel, test case by Jesper Cockx

{-# OPTIONS -v tc.term.exlam:20 #-}

abstract
  foo : Set₁
  foo = Set
    where
      AbstractSet₁ : Set₂
      AbstractSet₁ = Set₁
      f : Set → AbstractSet₁
      f = λ { _ → Set }

{-# NO_TERMINATION_CHECK #-}
loop : Set → Set
loop = λ { A → loop A }
