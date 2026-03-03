module Issue8443 where

record Precategory : Set₁ where
  field
    Ob : Set

open Precategory

postulate is-terminal : (C : Precategory) → C .Ob → Set

module _ (C : Precategory) where
  record Terminal : Set where
    field
      top  : C .Ob
      has⊤ : is-terminal C top

module _ (B : Precategory) {top} (term : is-terminal B top) where
  open Terminal {C = B} record{ has⊤ = term } hiding (top)
