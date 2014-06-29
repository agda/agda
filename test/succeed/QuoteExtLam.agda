
open import Common.Prelude
open import Common.Reflect
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

def₄ = primQNameDefinition (quote magic₄)

pattern `el x = el (lit 0) x
pattern `Nat  = `el (def (quote Nat) [])
pattern vArg x = arg (arginfo visible relevant) x
pattern _`→_ a b = `el (pi (vArg a) b)
pattern `Wrap a = `el (def (quote Wrap) (vArg a ∷ []))
pattern `⊥ = def (quote ⊥) []

expected₄ : Definition
expected₄ = funDef (funDef
  (`Wrap `⊥ `→ `Nat)
  (absurd-clause (vArg (con (quote wrap) (vArg absurd ∷ [])) ∷ [])
    ∷ []))

check₄ : def₄ ≡ expected₄
check₄ = refl

expected = ext-lam (absurd-clause (arg (arginfo visible relevant) absurd ∷ []) ∷ []) []

check₁ : quoteTerm magic₁ ≡ expected
check₁ = refl

check₂ : quoteTerm magic₂ ≡ expected
check₂ = refl

expectedDef : Definition
expectedDef =
  funDef (funDef
    (el (lit 0) (pi (arg (arginfo visible relevant) (el (lit 0) (def (quote ⊥) [])))
                    (el (lit 0) (def (quote Nat) []))))
    (absurd-clause (arg (arginfo visible relevant) absurd ∷ []) ∷ []))

check₃ : primQNameDefinition (quote magic₃) ≡ expectedDef
check₃ = refl