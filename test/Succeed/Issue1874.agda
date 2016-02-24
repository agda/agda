
module _ where

module LocalSetoidCalc (Node : Set) where
  module _ (A : Node) where
    module _IsRelatedTo_ where

module SGFunctorSetup (Obj₁ Obj₂ : Set) where
  open LocalSetoidCalc Obj₁ public renaming (module _IsRelatedTo_ to _IsRelatedTo₁_)
  open LocalSetoidCalc Obj₂ public renaming (module _IsRelatedTo_ to _IsRelatedTo₂_)

postulate X Y : Set
open SGFunctorSetup X Y
