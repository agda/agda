
module _ (A : Set) where

open import Issue1701.ModParamsToLose
module ParamA = Param A
open ParamA

failed : (A → A) → A → A
failed G = S.F
  module fails where
    module S = r A G
