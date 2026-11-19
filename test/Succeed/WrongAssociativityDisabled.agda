-- Andreas, 2026-11-18, issue #8750
-- The following pre/postfix operators have the wrong associativity, but the warning is off.

{-# OPTIONS --safe -Werror -WnoWrongAssociativity #-}

module WrongAssociativityDisabled where

infixl 42 foo_
infixr 42 _bar

data T : Set where
  foo_ _bar : T → T
