
open import Common.Prelude
open import Common.Reflection
open import Common.Equality

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

pattern
  `Nat  = def (quote Nat) []
  _`→_ a b = pi (vArg a) (abs "_" b)
  `Wrap a = def (quote Wrap) (vArg a ∷ [])
  `⊥ = def (quote ⊥) []

pattern
  expected₄ = funDef
    (absurdClause (vArg (con (quote wrap) (vArg absurd ∷ [])) ∷ [])
      ∷ [])

check₄ : OK
check₄ = checkDefinition (λ { expected₄ → true; _ → false }) magic₄

expected = extLam (absurdClause (arg (argInfo visible relevant) absurd ∷ []) ∷ []) []

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

pattern
  expectedDef = funDef (absurdClause (vArg absurd ∷ []) ∷ [])

check₃ : OK
check₃ = checkDefinition (λ { expectedDef → true; _ → false }) magic₃
