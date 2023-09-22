-- Andreas, 2023-07-01, issue #6711, raised and testcase by caryoscelus
-- Unbound builtins should not raise internal errors.

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    prj₁ : A
    prj₂ : B prj₁

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringUncons : String → Maybe (Σ Char (λ _ → String))

-- WAS: Internal error
--
-- Expected: No binding for builtin thing SIGMA...
