-- Symbolic anchors follow source modules, independently of staging and copying.
module RecordStageAnchors where

record R : Set₁ where
  Before : Set → Set
  Before X = X

  data D : Set where
    d : D

  module Nested where
    N : Set
    N = D

  record Inner : Set₁ where
    constructor inner
    field U : Set
    Helper : Set
    Helper = U
    field value : Helper

  -- A source module with this name must keep its qualifier.
  module record-stage where
    user : Set
    user = D

  module _ where
    anonymous : Set
    anonymous = D

  field A : Set

  private
    Hidden : Set
    Hidden = D

  module Middle where
    B : Set
    B = A

  module Alias = Middle

  X : Set
  X = Alias.B

  field C : X → Set

  After : Set
  After = Hidden

module Copy = R
open Copy renaming (Before to Renamed)

use : (r : R) → Set
use r = Renamed r (R.X r)
