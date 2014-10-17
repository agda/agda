
open import Common.Level
open import Common.Reflection
open import Common.Equality
open import Common.Prelude

postulate
  f : ∀ a → Set a

pattern varg  x = arg (argInfo visible relevant) x
pattern `lsuc x = set (def (quote lsuc) (varg x ∷ []))

thm : primQNameType (quote f) ≡
      el unknown (pi (varg (el (lit 0) (def (quote Level) [])))
                     (abs "a" (el (`lsuc (var 0 [])) (sort (set (var 0 []))))))
thm =  refl
