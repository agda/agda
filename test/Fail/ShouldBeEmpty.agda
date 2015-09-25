
module ShouldBeEmpty where

data Zero : Set where
data One : Set where
  one : One

ok : Zero -> One
ok ()

bad : One -> One
bad ()

