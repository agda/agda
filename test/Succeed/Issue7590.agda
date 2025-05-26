{-# OPTIONS --allow-unsolved-metas --type-in-type #-}

postulate Fill : {A : Set} → A

a b : (A : Set) → ? A
a = Fill
b = Fill

c d : (A : Set)(B : A → Set) → B ?
c = Fill
d = Fill

f g : ∀ x → ? ?
f = Fill
g = Fill
