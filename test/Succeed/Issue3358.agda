
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
  works : ∀ {G} → (x : [ G ]) → (x ∙ x) ≡ x
  fails : (x : [ G ]) → (x ∙ x) ≡ x
  -- WAS: No instance of type IsGroup [ G ]
