-- Subtyping is no longer supported for irrelevance.

f : {A B : Set} → (.A → B) → A → B
f g = λ .x → g x
