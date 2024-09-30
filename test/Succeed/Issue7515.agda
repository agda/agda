-- 2024-09-30. Andreas, issue #7515, test by Ulf
-- Demonstrate that generalization happens after macro expansion,
-- so quoting generalizable variables makes sense.

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.List

variable
  A B : Set

vArg : Term → Arg Term
vArg = arg (arg-info visible (modality relevant quantity-ω))

fun : List Name → Term
fun [] = def (quote ⊤) []
fun (x ∷ []) = def x []
fun (x ∷ xs) = pi (vArg (def x [])) (abs "_" (fun xs))

macro
  fn : List Name → Term → TC ⊤
  fn xs hole = unify (fun xs) hole

foldr : fn (quote A ∷ quote B ∷ quote B ∷ []) → fn (quote B ∷ []) → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

-- The type of foldr is polymorphic.

foldr' : {A B : Set} → (A → B → B) → B → List A → B
foldr' = foldr
