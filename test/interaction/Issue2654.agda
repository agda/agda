-- Andreas, 2017-07-24, issue #2654 reported by rntz
-- When splitting projections in an extended lambda,
-- we have to print them postfix, regardless of whether
-- the user chose --postfix-projections or not.

-- {-# OPTIONS --postfix-projections #-}
-- {-# OPTIONS -v interaction.case:60 #-}

open import Common.Product

dup : ∀{A : Set} (a : A) → A × A
dup = λ { x → {!!}  }  -- C-c C-c RET

-- Expected result after result splitting:
-- dup = λ { x .proj₁ → {!!} ; x .proj₂ → {!!}  }
