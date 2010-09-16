------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

module Reflection where

open import Data.Bool using (Bool); open Data.Bool.Bool
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary

------------------------------------------------------------------------
-- Names

-- Names.

postulate Name : Set

{-# BUILTIN QNAME Name #-}

private
  primitive
    primQNameEquality : Name → Name → Bool

-- Equality of names is decidable.

infix 4 _==_ _≟_

_==_ : Name → Name → Bool
_==_ = primQNameEquality

_≟_ : Decidable {A = Name} _≡_
s₁ ≟ s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

------------------------------------------------------------------------
-- Terms

-- Is the argument explicit?

Explicit? = Bool

-- Arguments.

data Arg A : Set where
  arg : Explicit? → A → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

-- Terms.

data Term : Set where
  -- Variable applied to arguments.
  var     : ℕ → List (Arg Term) → Term
  -- Constructor applied to arguments.
  con     : Name → List (Arg Term) → Term
  -- Identifier applied to arguments.
  def     : Name → List (Arg Term) → Term
  -- Explicit or implicit λ abstraction.
  lam     : Explicit? → Term → Term
  -- Pi-type.
  pi      : Arg Term → Term → Term
  -- An arbitrary sort (Set, for instance).
  sort    : Term
  -- Anything.
  unknown : Term

{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
