{-# OPTIONS --safe #-}
module LetPostulate where

_ : Set
_ =
  let
    postulate x : Set
  in x
