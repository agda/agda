
module ShouldBeApplicationOf where

data One : Set where one : One
data Two : Set where two : Two

f : One -> Two
f two = two

