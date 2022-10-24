record Model : Set₁ where
  field
    W : Set
    f : W → W → Set

theModel : {{m : Model}} → Model
theModel {{m}} = m

postulate instance m : Model

test : Model.W m → Set
test w = {w′ : _} → Model.f theModel w′ w
            -- ^ Meta should be instantiated to Model.W m
