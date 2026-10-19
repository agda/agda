module Issue8710.A where
postulate
  R : {A : Set} → A → A → Set
{-# BUILTIN REWRITE R #-}
