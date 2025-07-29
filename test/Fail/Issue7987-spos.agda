{-# OPTIONS --polarity #-}

_ = let @++ S = Set in S → S

-- Expected error: [VariableIsOfUnusablePolarity]
-- Variable S is bound with strictly positive polarity, so it cannot
-- be used here at a negative position
