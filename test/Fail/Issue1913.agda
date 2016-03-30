module _ where

module M where

  data D : Set where
    d : D

  private
    instance
      x : D
      x = d

! : ⦃ _ : M.D ⦄ → M.D
! ⦃ x ⦄ = x

y : M.D
y = !
