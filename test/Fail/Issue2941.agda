
record ⊤ : Set where constructor tt
data ⊥ : Set where

open import Agda.Builtin.Size

record Delay (F : Size → Set) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → F j
open Delay public

data Stream (A : Set) (i : Size) : Set where
 _∷_ : A → Delay (Stream A) i → Stream A i

concat : Stream ⊤ ∞ → Delay (Stream ⊥) ∞
concat (xs ∷ xss) = concat (force xss)

head : Stream ⊥ ∞ → ⊥
head (x ∷ xs) = x

units : ∀ {i} → Stream ⊤ i
units = tt ∷ λ where .force → units

false : ⊥
false = head (force (concat units))
