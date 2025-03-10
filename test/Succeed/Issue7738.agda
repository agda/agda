-- Test case by Malin Altenmüller

{-# OPTIONS --rewriting #-}

data One : Set where
  ⊤ : One

data P : One → One → Set where
  m : P ⊤ ⊤

{-# BUILTIN REWRITE P #-}

{-# REWRITE m #-}
