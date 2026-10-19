module Issue8710.B where
postulate
  S : {A : Set} → A → A → Set
{-# BUILTIN REWRITE S #-}
