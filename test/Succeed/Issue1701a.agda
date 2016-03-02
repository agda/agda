-- Andreas, 2015-10-26, issue reported by Wolfram Kahl
-- {-# OPTIONS -v scope.mod.inst:30 -v tc.mod.check:10 -v tc.mod.apply:80 #-}

module _ where

  module ModParamsRecord (A : Set) where
    record R (B : Set) : Set where
      field F : A → B

  module ModParamsToLoose (A : Set) where
    open ModParamsRecord

    private
      module M (B : Set) (G : A → B) where
        r : R A B
        r = record { F = G }

        module r = R r
    open M public

  module ModParamsLost (A : Set) where
    open ModParamsRecord
    open ModParamsToLoose A

    f : (A → A) → A → A
    f G = S.F
      where
        module S = r A G           -- expected |S.F : A → A|,
                                   -- WAS: but obtained |S.F : (B : Set) (G₁ : A → B) → A → B|
        -- module S = r            -- as expected: |S.F : (B : Set) (G₁ : A → B) → A → B|
        -- module S = R A (r A G)  -- as expected: |S.F : A → A|
