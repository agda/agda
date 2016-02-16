
open import Common.Level
open import Common.Reflection
open import Common.Equality
open import Common.Prelude

postulate
  f : ∀ a → Set a

pattern expectedType =
  pi (vArg (def (quote Level) []))
     (abs "a" (sort (set (var 0 []))))

ok : ⊤
ok = _

notOk : String
notOk = "not ok"

macro
  isExpected : QName → Tactic
  isExpected x hole =
    bindTC (getType x) λ
    { expectedType → give (quoteTerm ok)    hole
    ; t            → give (quoteTerm notOk) hole }

thm : ⊤
thm = isExpected f
