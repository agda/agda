-- {-# OPTIONS -v tc.lhs.problem:10 #-}
-- Do not normalize goals!
module Issue734 where

id : Set → Set
id A = A

g : (A : Set) → id A
g A = {!!}
-- goal should be displayed as "id A", not as "A"
