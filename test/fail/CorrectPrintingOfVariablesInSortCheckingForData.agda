-- 2012-02-22
module CorrectPrintingOfVariablesInSortCheckingForData where

data Bool : Set where 
  true false : Bool

if_then_else_ : {A : Set2} → Bool → A → A → A
if true then a else b = a
if false then a else b = b

data foo : (y : Bool) → if y then Set else Set 

data foo where
  bar : foo true
 
-- This should print
--   if y then Set else Set != Set of type Set₁
-- and not 
--   if @0 then ...