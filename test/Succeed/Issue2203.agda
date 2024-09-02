
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

-- setup

infixl 5 _>>=_
_>>=_ = bindTC

defToTerm : Name → Definition → List (Arg Term) → Term
defToTerm _ (function cs)   as = pat-lam cs as
defToTerm _ (data-cons d _) as = con d as
defToTerm _ _ _ = unknown

data Tm : Set where
  tm : Term → Tm

macro
  unfold : Name → Term → TC ⊤
  unfold x a = getDefinition x >>= λ d → unify a (defToTerm x d [])

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

Point = Vec Nat 3

renderBuffer : List Point → List Nat
renderBuffer [] = []
renderBuffer ((x ∷ y ∷ z ∷ []) ∷ xs) = x ∷ y ∷ z ∷ renderBuffer xs

renderBuffer' : List Point → List Nat
renderBuffer' = unfold renderBuffer

ps : List Point
ps = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []

open import Agda.Builtin.Equality

check : renderBuffer' ps ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
check = refl
