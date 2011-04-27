
module Common.Reflect where

open import Common.Prelude

postulate QName : Set
{-# BUILTIN QNAME QName #-}
primitive primQNameEquality : QName → QName → Bool

Hiding = Bool

data Arg A : Set where
  arg : Hiding → A → Arg A

{-# BUILTIN ARG Arg #-}
{-# BUILTIN ARGARG arg #-}

mutual
  data Term : Set where
    var     : Nat → Args → Term
    con     : QName → Args → Term
    def     : QName → Args → Term
    lam     : Hiding → Term → Term
    pi      : Arg Term → Term → Term
    sort    : Term
    unknown : Term

  Args = List (Arg Term)

{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
