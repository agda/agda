
open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.Sigma

magic₁ : ⊥ → Nat
magic₁ = λ ()

magic₂ : ⊥ → Nat
magic₂ = λ { () }

magic₃ : ⊥ → Nat
magic₃ ()

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

magic₄ : Wrap ⊥ → Nat
magic₄ (wrap ())

data OK : Set where
  ok : OK

bad : String
bad = "not good"

macro
  checkDefinition : (Definition → Bool) → QName → Tactic
  checkDefinition isOk f hole =
    bindTC (getDefinition f) λ def →
    give (if isOk def then quoteTerm ok else quoteTerm bad) hole

pattern `Nat  = def (quote Nat) []
pattern _`→_ a b = pi (vArg a) (abs "_" b)
pattern `Wrap a = def (quote Wrap) (vArg a ∷ [])
pattern `⊥ = def (quote ⊥) []

pattern expected₄ = funDef
  (absurdClause (("()" , vArg `⊥) ∷ []) (vArg (con (quote wrap) (vArg absurd ∷ [])) ∷ [])
  ∷ [])

check₄ : OK
check₄ = checkDefinition (λ { expected₄ → true; _ → false }) magic₄

expected = extLam (absurdClause (("()" , vArg `⊥) ∷ []) (arg (argInfo visible relevant) absurd ∷ []) ∷ []) []

macro

  quoteTermNormalised : Term → Term → TC ⊤
  quoteTermNormalised t hole =
    bindTC (normalise t) λ t →
    bindTC (quoteTC t) λ t →
    unify hole t

check₁ : quoteTermNormalised magic₁ ≡ expected
check₁ = refl

check₂ : quoteTermNormalised magic₂ ≡ expected
check₂ = refl

pattern expectedDef =
  funDef (absurdClause (("()" , vArg `⊥) ∷ []) (vArg absurd ∷ []) ∷ [])

check₃ : OK
check₃ = checkDefinition (λ { expectedDef → true; _ → false }) magic₃
