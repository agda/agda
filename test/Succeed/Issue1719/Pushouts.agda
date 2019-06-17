{-# OPTIONS --without-K --rewriting --confluence-check #-}

module Issue1719.Pushouts where

open import Issue1719.Common
open import Issue1719.Spans

postulate
  Pushout : (d : Span) → Set
  left : {d : Span} → (Span.A d) → Pushout d
  right : {d : Span} → (Span.B d) → Pushout d
  glue : {d : Span} → (c : Span.C d) → left (Span.f d c) == right (Span.g d c) :> Pushout d

module _ {d : Span} {l} {P : Pushout d → Set l}
  (left* : (a : Span.A d) → P (left a))
  (right* : (b : Span.B d) → P (right b))
  (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c) [ P ↓ glue c ]) where

  postulate
    Pushout-elim : (x : Pushout d) → P x
    Pushout-left-β : (a : Span.A d) → Pushout-elim (left a) ↦ left* a
    {-# REWRITE Pushout-left-β #-}
    Pushout-right-β : (b : Span.B d) → Pushout-elim (right b) ↦ right* b
    {-# REWRITE Pushout-right-β #-}
    Pushout-glue-β : (c : Span.C d) → ap Pushout-elim (glue c) ↦ glue* c
    {-# REWRITE Pushout-glue-β #-}
