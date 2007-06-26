------------------------------------------------------------------------
-- Sketch of an interface for metaprogramming
------------------------------------------------------------------------

module Meta where

open import Logic
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

infixl 10 _·_
infix  5  $_

------------------------------------------------------------------------
-- Atoms

-- An _abstract_ type which can represent arbitrary code (in Set).

postulate
  Atom   : Set -> Set1

  -- Unquote/splice.

  $-atom : forall {a} -> Atom a -> a

------------------------------------------------------------------------
-- Expressions

-- A _concrete_ type which can represent arbitrary code (in Set), but
-- uses Atom for stuff which we do not have a good representation for.

-- Currently an expression is either an application or an atom, but
-- this can (should) be extended to include more of the core
-- expression language.

mutual

  data Expr : Set -> Set1 where
    atom :  forall {a} -> Atom a -> Expr a
    _·_  :  forall {a} {b : a -> Set}
         -> Expr ((x : a) -> b x)
         -> (x : Expr a) -> Expr (b ($ x))

  -- Unquote/splice.

  $_  : forall {a} -> Expr a -> a
  $ (atom a) = $-atom a
  $ (f · x)  = ($ f) ($ x)

postulate

  -- Quote. The intention is that ⟦ f x ⟧ = atom a₁ · atom a₂, where
  -- $-atom a₁ ≡ f and $-atom a₂ ≡ x. (If f and x are both names.)

  ⟦_⟧ : forall {a} -> a -> Expr a

  -- Decidable equality on Expr.

  _≟_ : forall {a} (x y : Expr a) -> Dec (x ≡₁ y)

  -- A total order is probably also a good idea.

------------------------------------------------------------------------
-- Properties

-- Are these properties sound, or should they be weakened in some way?

postulate
  prop-left-inverse : forall {a} (x : a) -> $ ⟦ x ⟧ ≡ x

------------------------------------------------------------------------
-- Problems with the above sketch

-- Note that x ≡ y ⇒ ⟦ x ⟧ ≡ ⟦ y ⟧. Hence ⟦ n + 0 ⟧ ≡ ⟦ 0 + n ⟧. The
-- library above, if implemented as intended, would hence yield an
-- inconsistency.
