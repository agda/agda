-- Andreas, 2016-06-20
-- Issue #1653 reported by Jesper
-- Fixed by Ulf's AIM XXIII code sprint "instantiating module parameters"

open import Common.Equality

module _ (A : Set₁) where

  -- Matching on refl works with new instantiateable module parameters.

  test : A ≡ Set → Set₁
  test refl = A

  -- Case splitting thus should also work.

  foo : A ≡ Set → Set₁
  foo e = {!e!} -- C-c C-c
