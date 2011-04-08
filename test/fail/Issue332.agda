module Issue332 where

id : {A : Set} → A → A
id x = x

syntax id x = id x -- This makes parsing id x ambiguous




