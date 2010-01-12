module LateMetaVariableInstantiation where

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

postulate
  yippie : (A : Set) → A

slow : (A : Set) → ℕ → A
slow A zero    = yippie A
slow A (suc n) = slow _ n

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

foo : slow ℕ 1000 ≡ yippie ℕ
foo = refl

-- Consider the function slow. Previously normalisation of slow n
-- seemed to take time proportional to n². The reason was that, even
-- though the meta-variable corresponding to the underscore was
-- solved, the stored code still contained a meta-variable:

--   slow A (suc n) = slow (_173 A n) n

-- (For some value of 173.) The evaluation proceeded as follows:

--   slow A 1000 =
--   slow (_173 A 999) 999 =
--   slow (_173 (_173 A 999) 998) 998 =
--   ...

-- Furthermore, in every iteration the Set argument was traversed, to
-- see if there was any de Bruijn index to raise.
