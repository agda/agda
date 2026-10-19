module Issue3358 where

open import Agda.Builtin.Equality

record IsGroup (G : Set) : Set where
  field _∙_ : G → G → G

open IsGroup ⦃ ... ⦄

record Group : Set₁ where
  field G       : Set
        ⦃ IsG ⦄ : IsGroup G

open Group using () renaming (G to [_])

variable
  G : Group

postulate
  -- used to be succesful, requires eta-expanding the non-instance
  -- argument to find an isRG instance. now rejected
  fails : ∀ {G} → (x : [ G ]) → (x ∙ x) ≡ x
