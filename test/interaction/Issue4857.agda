{-# OPTIONS --show-implicit #-}

module _ where

postulate
  R : Set

module ModuleB where

  module NotRecordB (r : R) where
    postulate notfieldB : Set

  open module NotRecBI {{r : R}} = NotRecordB r public

  record RecordB : Set₁ where
    field
      fieldB : Set

  open module RecBI {{r : RecordB}} = RecordB r public

open module ModBA = ModuleB

postulate
  myRecB : RecordB
  myR    : R

test₀ : fieldB {{myRecB}}
test₀ = {!!}

test₁ : ModuleB.RecordB.fieldB myRecB
test₁ = {!!}

test₂ : notfieldB {{myR}}
test₂ = {!!}

test₃ : ModuleB.NotRecordB.notfieldB myR
test₃ = {!!}
