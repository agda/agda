module TelescopingLet1 where

f : (let ★ = Set) (A : ★) → A → A
f A x = x

data X : ★ where
