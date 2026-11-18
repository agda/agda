-- Andreas, 2026-11-18, issue #8750
-- Warn about wrong fixity declaration for prefix and postfix operators.

module WrongAssociativity where

infixl 42 foo_ _and_
infixr 42 _bar goodPrefix_ _or_
infixl 42 _goodPostfix
infix  42 plainPrefix_ _plainPostfix _plainInfix_

data T : Set where
  zero : T
  foo_ _bar goodPrefix_ _goodPostfix plainPrefix_ _plainPostfix : T → T
  _and_ _or_ _plainInfix_ : T → T → T

prefix-chain : T
prefix-chain = foo foo zero

postfix-chain : T
postfix-chain = zero bar bar

custom : T → T
custom x = x

syntax custom x = x custom-postfix
infixr -0.5 custom

module Original where
  plain : T → T
  plain x = x

  customPrefix : T → T
  customPrefix x = x

  infixr 40 customPrefix
  syntax customPrefix x = custom-prefix x

open Original renaming
  ( plain        to infixl 12 renamed_
  ; customPrefix to infixl 13 _renamedCustom
  )
