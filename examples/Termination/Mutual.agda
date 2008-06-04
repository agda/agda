-- examples for termination checking mutual recursion

module Mutual where

mutual

  data Even : Set where
    zeroE : Even
    succE : Odd -> Even

  data Odd : Set where
    succO : Even -> Odd

mutual
 
  addOO : Odd -> Odd -> Even
  addOO (succO x) y = succE (addEO x y)

  addEO : Even -> Odd -> Odd
  addEO zeroE y = y
  addEO (succE x) y = succO (addOO x y)

