{-# OPTIONS  --sized-types --show-implicit #-}

module SizedNatAnnotated where

open import Size

data Nat : {i : Size} -> Set where
  zero : {i : Size} -> Nat {↑ i}
  suc  : {i : Size} -> Nat {i} -> Nat {↑ i}

-- subtraction is non size increasing
sub : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
sub .{↑ i} (zero {i})  n       = zero {i}
sub .{↑ i} (suc {i} m) zero    = suc {i} m
sub .{↑ i} (suc {i} m) (suc n) = sub {i} m n

-- div' m n  computes  ceiling(m/(n+1))
div' : {i : Size} -> Nat {i} -> Nat -> Nat {i}
div' .{↑ i} (zero {i})  n = zero {i}
div' .{↑ i} (suc {i} m) n = suc  {i} (div' {i} (sub {i} m n) n)

