
module Issue620 where

module A where
  postulate _+_*_ : Set → Set → Set → Set

postulate X : Set

2X : Set
2X = X A.+ X * X
