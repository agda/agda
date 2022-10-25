-- Andreas, 2022-09-30, issue #6001
-- Testcase by @tomdjong, Jakob Bruenker, Amelia

-- Cubical extra-clauses cannot be generated unless
-- target is known to be fibrant.

{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

data Foo {A : Set} : A → Set where
  con : (x : A) → Foo x

bug : ∀ {A : Set} {a : A} {p : Foo a} → {!!}
bug {p = con _} = {!!}

-- This used to crash on the 2.6.3 development version,
-- but should produce just unsolved metas (like on 2.6.2).
