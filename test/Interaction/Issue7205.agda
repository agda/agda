{-# OPTIONS --polarity #-}

module Issue7205 where

data Head : Set where
  head : Head

Whole : @++ Set → Head → Set
Whole = {! !}

Body : @++ Set → Head → Set
Body X _ = {! !}

Locked : @++ Set → Head → Set
Locked X _ = {! !} → Head

record Exp (rec : @++ Set → Set) : Set where
  inductive
  no-eta-equality
  field
    shape  : Head
    whole  : Whole  (rec (Exp rec)) shape
    body   : Body   (rec (Exp rec)) shape
    locked : Locked (rec (Exp rec)) shape
