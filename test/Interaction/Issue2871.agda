-- Andreas, 2017-12-16, issue #2871

-- If there is nothing to result-split, introduce trailing hidden args.

-- {-# OPTIONS -v interaction.case:40 #-}

data Fun (A : Set) : Set where
  mkFun : (A → A) → Fun A

test : ∀ {A : Set} → Fun A
test = {!!}  -- C-c C-x C-h C-c C-c RET

-- Works also with C-c C-c RET
--
-- Expected:
-- test {A} = {!!}
