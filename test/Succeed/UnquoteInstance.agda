
open import Common.Prelude
open import Common.Reflection
open import Common.Equality

data Dec {a} (A : Set a) : Set a where
  yes : A → Dec A
  no  : Dec A

record Eq {a} (A : Set a) : Set a where
  constructor eqDict
  field
    _==_ : (x y : A) → Dec (x ≡ y)

module M {a} {A : Set a} {{EqA : Eq A}} where
  _==_ : (x y : A) → Dec (x ≡ y)
  _==_ = Eq._==_ EqA

open Eq {{...}}

private
  eqNat : (x y : Nat) → Dec (x ≡ y)
  eqNat zero zero = yes refl
  eqNat zero (suc y) = no
  eqNat (suc x) zero = no
  eqNat (suc x) (suc y) with eqNat x y
  eqNat (suc x) (suc .x) | yes refl = yes refl
  ... | no     = no

  eqBool : (x y : Bool) → Dec (x ≡ y)
  eqBool true true = yes refl
  eqBool true false = no
  eqBool false true = no
  eqBool false false = yes refl

unquoteDecl EqNat = define (iArg EqNat)
  (funDef (def (quote Eq) (vArg (def (quote Nat) []) ∷ []))
          (clause [] [] (con (quote eqDict) (vArg (def (quote eqNat) []) ∷ [])) ∷ []))

instance
  EqBool : Eq Bool
  unquoteDef EqBool =
    defineFun EqBool (clause [] [] (con (quote eqDict) (vArg (def (quote eqBool) []) ∷ [])) ∷ [])

id : {A : Set} → A → A
id x = x

tm : QName → Term
tm eq = def (quote id) (vArg (def eq (vArg (lit (nat 0)) ∷ vArg (lit (nat 1)) ∷ [])) ∷ [])

tm₂ : QName → Term
tm₂ eq = def eq (iArg (def (quote EqNat) []) ∷ vArg (lit (nat 0)) ∷ vArg (lit (nat 1)) ∷ [])

_==′_ : ∀ {a} {A : Set a} {{EqA : Eq A}} (x y : A) → Dec (x ≡ y)
_==′_ = _==_

ok₁ : Dec (0 ≡ 1)
ok₁ = unquote (give (tm (quote _==′_)))

ok₂ : Dec (0 ≡ 1)
ok₂ = unquote (give (tm₂ (quote _==_)))

ok₃ : Dec (0 ≡ 1)
ok₃ = unquote (give (tm (quote M._==_)))

ok₄ : Dec (true ≡ false)
ok₄ = true == false

ok₅ : Dec (2 ≡ 2)
ok₅ = 2 == 2

-- Was bad.
bad : Dec (0 ≡ 1)
bad = unquote (give (tm (quote _==_)))
