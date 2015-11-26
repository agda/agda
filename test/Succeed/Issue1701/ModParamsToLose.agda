
module Issue1701.ModParamsToLose where

module Param (A : Set) where

  module R (B : Set) (G : A → B) where
    F = G

  private
   module Tmp (B : Set) (G : A → B) where
    module r = R B G

  open Tmp public

module Works (A : Set) where
  module ParamA = Param A
  open ParamA

  works : (A → A) → A → A
  works G = S.F
    module works where
      module S = r A G
