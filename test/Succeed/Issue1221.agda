
open import Common.Level
open import Common.Reflection
open import Common.Equality
open import Common.Prelude
open import Common.TC

postulate
  f : ∀ a → Set a

pattern varg  x = arg (argInfo visible relevant) x
pattern `lsuc x = set (def (quote lsuc) (varg x ∷ []))

pattern expectedType =
  el unknown (pi (varg (el (lit 0) (def (quote Level) [])))
             (abs "a" (el (`lsuc (var 0 [])) (sort (set (var 0 []))))))

ok : ⊤
ok = _

notOk : String
notOk = "not ok"

macro
  isExpected : QName → Tactic
  isExpected x hole =
    bindTC (getType x) λ
    { expectedType → give (quoteTerm ok)    hole
    ; (el _ t)     → give (quoteTerm notOk) hole }

thm : ⊤
thm = isExpected f
