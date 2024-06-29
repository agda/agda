
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

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → returnTC (defToTerm f f' args)
derefImmediate x = returnTC x

macro
  reflect : ∀ {ℓ} {t : Set ℓ} → t → Term → TC ⊤
  reflect x a = quoteTC x >>= derefImmediate >>= quoteTC >>= unify a

  unfold : Name → Term → TC ⊤
  unfold x a = getDefinition x >>= λ d → unify a (defToTerm x d [])

-- crash

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

vid vid' : ∀ n → Vec Nat n → Vec Nat n
vid n [] = []
vid n (x ∷ xs) = x ∷ xs

vid' = unfold vid

crash : Term
crash = reflect vid

len : ∀ {n} → Vec Nat n → Nat
len [] = 0
len (x ∷ xs) = suc (len xs)

-- Forces different order in clause tel and patterns
f f' : ∀ n → Vec Nat n → Vec Nat n → Nat
f n xs [] = n
f n xs (y ∷ ys) = n + y + len xs + len ys

f' = unfold f
