{-# OPTIONS --copatterns #-}

module SplitResult where

open import Common.Product

test : {A B : Set} (a : A) (b : B) → A × B
test a b = {!!}

testFun : {A B : Set} (a : A) (b : B) → A × B
testFun = {!!}

