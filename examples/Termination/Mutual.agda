-- examples for termination checking mutual recursion

module Mutual where

data Odd : Set

data Even : Set where
  zeroE : Even
  succE : Odd -> Even

data Odd where
  succO : Even -> Odd

addEO : Even -> Odd -> Odd

addOO : Odd -> Odd -> Even
addOO (succO x) y = succE (addEO x y)

addEO zeroE y = y
addEO (succE x) y = succO (addOO x y)

