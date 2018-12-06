
module _ where

import Imports.Issue1913-M as M

module _ where

  import Imports.Issue1913-I as I

  accepted₁ : M.D
  accepted₁ = I.x

! : ⦃ _ : M.D ⦄ → M.D
! ⦃ x ⦄ = x

accepted₂ : M.D
accepted₂ = !

-- rejected : M.D
-- rejected = I.x
