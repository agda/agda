
module _ where

data X : Set where
data R (x : X) : Set where

module SUListSepElemTypes where

  module M2 (Elem : Set) where
    data InclWith : Set where

  module M1 where
    module InclZip1 (R : X → Set) where
      open M2 X public
      module InclZipUnion (Y : Set) where

module SepElemTypes = SUListSepElemTypes

module Zip⊆ = SepElemTypes.M1.InclZip1 R
module Zip⊆∪ = Zip⊆.InclZipUnion X
