
module _ where

-- Should not be able to give by name
id : {_ = A : Set} → A → A
id x = x

works : (X : Set) → X → X
works X = id {X}

fails : (X : Set) → X → X
fails X = id {A = X}
