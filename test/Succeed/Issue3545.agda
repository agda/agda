module Issue3545 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Common.IO

createElem : Nat → Set
createElem n = Nat

{-# NOINLINE createElem #-}

{-# COMPILE JS createElem = function (x0) {
    return x0;
} #-}

-- WAS: silently accepted
-- WANT: `createElem` is going to be erased; don't do that!

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

{-# COMPILE GHC map = \ _ _ _ _ -> Prelude.map #-}

-- `map` however is not erased so this should not raise a warning.

value : List Set
value = map (λ n → createElem n) (1 ∷ 1 ∷ [])
