{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.String where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringUncons   : String → Maybe (Σ Char (λ _ → String))
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowChar       : Char → String
  primShowString     : String → String
  primShowNat        : Nat → String

{-# COMPILE JS primStringUncons = function(x) {
   if (x === "") { return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"]; };
   return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](z_jAgda_Agda_Builtin_Sigma["_,_"](x.charAt(0))(x.slice(1)));
   }
 #-}
{-# COMPILE JS primStringToList = function(x) { return x.split(""); } #-}
{-# COMPILE JS primStringFromList = function(x) { return x.join(""); } #-}
{-# COMPILE JS primStringAppend = function(x) { return function(y) { return x+y; }; } #-}
{-# COMPILE JS primStringEquality = function(x) { return function(y) { return x===y; }; } #-}
{-# COMPILE JS primShowChar = function(x) { return JSON.stringify(x); } #-}
{-# COMPILE JS primShowString = function(x) { return JSON.stringify(x); } #-}
{-# COMPILE JS primShowNat = function(x) { return JSON.stringify(x); } #-}
