
module Common.Reflect where

open import Common.Prelude renaming (Nat to ℕ)

postulate QName : Set
{-# BUILTIN QNAME QName #-}
primitive primQNameEquality : QName → QName → Bool

data Hiding : Set where
  hidden visible : Hiding

{-# BUILTIN HIDING  Hiding  #-}
{-# BUILTIN HIDDEN  hidden  #-}
{-# BUILTIN VISIBLE visible #-}

-- relevant    the argument is (possibly) relevant at compile-time
-- nonStrict   the argument may never flow into evaluation position.
--             Therefore, it is irrelevant at run-time.
--             It is treated relevantly during equality checking.
-- irrelevant  the argument is irrelevant at compile- and runtime
-- forced      the argument can be skipped during equality checking
data Relevance : Set where
  relevant nonStrict irrelevant forced : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN NONSTRICT  nonStrict  #-}
{-# BUILTIN IRRELEVANT irrelevant #-}
{-# BUILTIN FORCED     forced     #-}

data Arg A : Set where
  arg : Hiding → Relevance → A → Arg A

{-# BUILTIN ARG Arg #-}
{-# BUILTIN ARGARG arg #-}

mutual
  data Term : Set where
    var     : ℕ → Args → Term
    con     : QName → Args → Term
    def     : QName → Args → Term
    lam     : Hiding → Term → Term
    pi      : Arg Type → Type → Term
    sort    : Sort → Term
    unknown : Term

  Args = List (Arg Term)

  data Type : Set where
    el : Sort → Term → Type

  data Sort : Set where
    set     : Term → Sort
    lit     : ℕ → Sort
    unknown : Sort

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}
