
{-# OPTIONS --without-K --rewriting --confluence-check #-}

open import Issue1719.Common
open import Issue1719.Spans
open import Issue1719.Pushouts

module _ {d : Span} {l} {P : Pushout d → Set l}
  (left* : (a : Span.A d) → P (left a))
  (right* : (b : Span.B d) → P (right b))
  (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c) [ P ↓ glue c ]) where

  test : (a : Span.A d) → Pushout-elim {P = P} left* right* glue* (left a) ↦ left* a
  test a = idr
