{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

module Issue1719.Spans where

open import Issue1719.Common

record Span : Set₁ where
  constructor span
  field
    A B C : Set
    f : C → A
    g : C → B
open Span public
