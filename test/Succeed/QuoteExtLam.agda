
open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Common.TC

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

pattern `el x = el (lit 0) x
pattern `Nat  = `el (def (quote Nat) [])
pattern _`→_ a b = `el (pi (vArg a) (abs "_" b))
pattern `Wrap a = `el (def (quote Wrap) (vArg a ∷ []))
pattern `⊥ = def (quote ⊥) []

pattern expected₄ = funDef (funDef
  (`Wrap `⊥ `→ `Nat)
  (absurdClause (vArg (con (quote wrap) (vArg absurd ∷ [])) ∷ [])
    ∷ []))

check₄ : OK
check₄ = checkDefinition (λ { expected₄ → true; _ → false }) magic₄

expected = extLam (absurdClause (arg (argInfo visible relevant) absurd ∷ []) ∷ []) []

check₁ : quoteTerm magic₁ ≡ expected
check₁ = refl

check₂ : quoteTerm magic₂ ≡ expected
check₂ = refl

pattern expectedDef =
  funDef (funDef
    (el (lit 0) (pi (arg (argInfo visible relevant) (el (lit 0) (def (quote ⊥) [])))
                    (abs "_" (el (lit 0) (def (quote Nat) [])))))
    (absurdClause (arg (argInfo visible relevant) absurd ∷ []) ∷ []))

check₃ : OK
check₃ = checkDefinition (λ { expectedDef → true; _ → false }) magic₃
