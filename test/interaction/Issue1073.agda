module _ (A : Set) (Sing : A → Set) (F : (a : A) → Sing a → Set) where

test : {a : A} → Sing a → Set
test s = F {!!} s

-- WAS: C-c C-s inserts a, which produces a scope error
-- Instead, it should insert _
