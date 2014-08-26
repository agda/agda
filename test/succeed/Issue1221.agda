
open import Common.Level
open import Common.Reflect
open import Common.Equality
open import Common.Prelude

postulate
  f : ∀ a → Set a

pattern varg  x = arg (arginfo visible relevant) x
pattern `lsuc x = set (def (quote lsuc) (varg x ∷ []))

thm : primQNameType (quote f) ≡
      el unknown (pi (varg (el (lit 0) (def (quote Level) [])))
                     (el (`lsuc (var 0 [])) (sort (set (var 0 [])))))
thm =  refl
