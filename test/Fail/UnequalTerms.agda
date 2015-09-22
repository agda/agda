
module UnequalTerms where

data Zero : Set where
data One  : Set where one : One

err1 : Zero
err1 = one

err2 : One -> One
err2 = \(x : Zero) -> one

