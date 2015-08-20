
module _ where

open import Common.Equality

postulate
  _def_ _more_ _less_ : Set → Set → Set
  X : Set

infix 21 _more_
-- default fixity should be 20
infix 19 _less_

test : (X more X def X less X) ≡ _less_ (_def_ (_more_ X X) X) X
test = refl

module NoFix where
  data NoFix : Set₁ where
    _+_ : Set → Set → NoFix

module YesFix where
  data YesFix : Set₁ where
    _+_ : Set → Set → YesFix
  infix 10 _+_

open NoFix
open YesFix

-- overloaded _+_ should get fixity 10
test₂ : X less X + X ≡ NoFix._+_ (_less_ X X) X
test₂ = refl

