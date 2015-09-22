module TelescopingLet2 where

f : (let ★ = Set) (A : ★) → A → Set₁
f A x = ★
-- should fail, since ★ is not in scope in the definition
