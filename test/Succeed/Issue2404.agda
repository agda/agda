open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.List

infixl 5 _>>=_
_>>=_ = bindTC
pure = returnTC


defToTerm : Name → Definition → List (Arg Term) → Term
defToTerm _ (function cs)   as = pat-lam cs as
defToTerm _ (data-cons d _) as = con d as
defToTerm _ _ _ = unknown

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → pure (defToTerm f f' args)
derefImmediate x = pure x

macro
  reflect : ∀ {ℓ} {t : Set ℓ} → t → Type → TC ⊤
  reflect {_} {t} x ty = quoteTC x >>= derefImmediate >>= λ x' → quoteTC t >>= checkType x' >>= quoteTC >>= unify ty
  -- reflect {_} {t} x ty = quoteTC x >>= derefImmediate >>= quoteTC >>= unify ty


data Maybe {ℓ} (t : Set ℓ) : Set ℓ where
  just : t → Maybe t
  nothing : Maybe t

listToMaybe : ∀ {ℓ} {t : Set ℓ} → List t → Maybe t
listToMaybe [] = nothing
listToMaybe (x ∷ _) = just x

record Show {ℓ} (t : Set ℓ) : Set ℓ where
  field
     show : t → String

open Show {{...}}

instance
  showN : Show Nat
  showN = record { show = λ _ → "nat" }

  mShow : ∀ {ℓ} {t : Set ℓ} → {{_ : Show t}} → Show (Maybe t)
  mShow = record {
      show = λ { (just x) → show x ;
                 _ → "nothing" }
    }


prog : String
prog =
  let
    x : List Nat
    x = 3 ∷ []
  in
  show (listToMaybe x)

example : Term
example = reflect prog
