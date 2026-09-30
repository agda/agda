-- Andreas, 2016-10-04, issue #2236
-- Result splitting should not insert hidden arguments visibly

-- {-# OPTIONS -v interaction.case:100 #-}
-- {-# OPTIONS -v tc.cover:100 #-}
-- {-# OPTIONS -v reify.clause:100 #-}
-- {-# OPTIONS -v reify.implicit:100 #-}

splitMe : (A : Set) {B : Set} → Set
splitMe = {!!}  -- C-c C-c RET inserts hidden {B}

splitMe' : (A : Set) {B : Set} (C : Set) {D : Set} → Set
splitMe' = {!!}  -- C-c C-c RET inserts hidden {B} and {D}

splitMe'' : {B : Set} (C : Set) {D : Set} → Set
splitMe'' = {!!}  -- C-c C-c RET inserts hidden {D}

postulate
  N : Set
  P : N → Set

test : (A : Set) → ∀ {n} → P n → Set
test = {!!} -- C-c C-c RET inserts hidden {n}

-- Correct is:
-- No hidden arguments inserted on lhs.
