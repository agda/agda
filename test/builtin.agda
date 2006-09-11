module Builtin where

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

postulate
  Integer : Set
  String  : Set

{-# BUILTIN INTEGER Integer #-}
{-# BUILTIN STRING  String  #-}

primitive
  integerPlus   : Integer -> Integer -> Integer
  integerMinus  : Integer -> Integer -> Integer
  integerEquals : Integer -> Integer -> Bool

(+)  = integerPlus
(==) = integerEquals
