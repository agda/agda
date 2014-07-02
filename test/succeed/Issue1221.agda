
open import Common.Level
open import Common.Reflect
open import Common.Equality
open import Common.Prelude

postulate
  f : ∀ a → Set a

thm : primQNameType (quote f) ≡
      el unknown (pi (arg (arginfo visible relevant) (el (lit 0) (def (quote Level) [])))
                     (el unknown (sort (set (var 0 [])))))
thm = refl
