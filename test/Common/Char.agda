{-# OPTIONS --without-K #-}
module Common.Char where

open import Agda.Builtin.Char public
open import Common.Bool

charEq : Char -> Char -> Bool
charEq = primCharEquality

