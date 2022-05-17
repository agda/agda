..
  ::
  module language.coverage-checking where

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.String

.. _coverage-checking:

*****************
Coverage Checking
*****************

To ensure completeness of definitions by pattern matching, Agda
performs a coverage check on each definition by pattern matching. This
page explains how this coverage check works by starting from simple
examples and building up to the general case.

Single match on a non-indexed datatype
--------------------------------------

When a :ref:`function definition <function-definitions>` pattern
matches on a single argument of a simple (i.e. non-indexed)
:ref:`datatype <data-types>`, there should be a clause for each
constructor. For example:

::

  data TrafficLight : Set where
    red yellow green : TrafficLight

  go : TrafficLight → Bool
  go red    = false
  go yellow = false
  go green  = true

Alternatively, one or more cases may be replaced by a *catchall
clause* that uses a variable pattern or a wildcard pattern `_`.
In this case, the catchall clause should be last.

::

  go' : TrafficLight → Bool
  go' green = true
  go' _     = false

.. note::

  When the `--exact-split` flag is enabled, catchall clauses should be
  marked explicitly by a :ref:`catchall pragma <catchall-pragma>`
  (``{-# CATCHALL #-}``).

The coverage check can be turned off for an individual definition by
putting a ``{-# NON_COVERING #-}`` pragma immediately in front of the
type signature.

::

  {-# NON_COVERING #-}
  go'' : TrafficLight → Bool
  go'' red   = false
  go'' green = true

In the special case of a datatype with no constructors (i.e. an empty
type), there should be a single *absurd clause* with an absurd pattern
`()` and no right-hand side.

::

  data ⊥ : Set where
    -- no constructors

  magic : {A : Set} → ⊥ → A
  magic ()


Matching on multiple arguments
------------------------------

If a function matches on several arguments, there should be a case for
each possible combinations of constructors.

::

  sameColor : TrafficLight → TrafficLight → Bool
  sameColor red    red    = true
  sameColor red    yellow = false
  sameColor red    green  = false
  sameColor yellow red    = false
  sameColor yellow yellow = true
  sameColor yellow green  = false
  sameColor green  red    = false
  sameColor green  yellow = false
  sameColor green  green  = true

Again, one or more cases may be replaced by a catchall clause.

::

  sameColor' : TrafficLight → TrafficLight → Bool
  sameColor' red    red    = true
  sameColor' yellow yellow = true
  sameColor' green  green  = true
  sameColor' _      _      = false

Copattern matching
------------------

Functions that return an element of a :ref:`record type
<record-types>` can use :ref:`copatterns <copatterns>` to give the
individual fields. The coverage check will ensure that there is a
single case for each field of the record type. For example:

::

  record Person : Set where
    field
      name : String
      age  : Nat
  open Person

  bob : Person
  name bob = "Bob"
  age  bob = 25

Absurd copatterns or wildcard copatterns are not supported.

Matching on indexed datatypes
-----------------------------

When a function definition matches on an argument of an indexed
datatype, the following conditions should be satisfied:

- For each clause that matches on a constructor pattern ``c u₁ … uₙ``,
  the indices of the type of the pattern should be unifiable with the
  indices of the datatype being matched on.

- For each constructor ``c`` that does not appear in a clause,
  unification of the indices of the type of the constructor with the
  indices of the datatype should end in a conflict.

For example, consider the definition of the ``head`` function on
vectors:

::

  data Vec (A : Set) : Nat → Set where
    []  : Vec A 0
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  head : ∀ {A m} → Vec A (suc m) → A
  head (x ∷ xs) = x

The type of the pattern ``x ∷ xs`` is ``Vec A (suc n)``, which is
unifiable with the type ``Vec A (suc m)``. Meanwhile, unification of
the type ``Vec A 0`` of the constructor ``[]`` with the type ``Vec A
(suc n)`` results in a conflict between ``0`` and ``suc n``, so there
is no case for ``[]``.

In case a function matches on several arguments and one or more of
them are of indexed datatypes, only those combinations of arguments
should be considered where the indices do not lead to a conflict. For
example, consider the ``zipWith`` function on vectors:

::

  zipWith : ∀ {A B C m} → (A → B → C) → Vec A m → Vec B m → Vec C m
  zipWith f []       []       = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

Since both input vectors have the same length ``m``, there is are no
cases for the combinations where one vector has length ``0`` and the
other has length ``suc n``.

In the special case where unification ends in a conflict for *all*
constructors, there should be a single absurd clase (as for an empty
type). For example:

::

  data Fin : Nat → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)

  no-fin-zero : Fin 0 → ⊥
  no-fin-zero ()

In many common cases, absurd clauses may be omitted as long as the
remaining clauses reveal sufficient information to indicate what
arguments to case split on. As an example, consider the definition of
the ``lookup`` function for vectors:

::

  lookup : ∀ {A} {n} → Vec A n → Fin n → A
  lookup []       ()
  lookup (x ∷ xs) zero    = x
  lookup (x ∷ xs) (suc i) = lookup xs i

This definition pattern matches on both its (explicit) arguments in
both the absurd clause and the two regular clauses. Hence it is
allowed to leave out the absurd clause from the definition:

::

  lookup' : ∀ {A} {n} → Vec A n → Fin n → A
  lookup' (x ∷ xs) zero    = x
  lookup' (x ∷ xs) (suc i) = lookup' xs i

Refer to the next section for a precise explanation of when an absurd
clause may be omitted.

General case
------------

In the general case, the coverage checker constructs a :ref:`case tree
<case-trees>` from the definition given by the user. It then ensures
that the following properties are satisfied:

- The non-absurd clauses of a definition should arise as the leaves of
  the case tree.

- The absurd clauses of a definition should arise as the internal
  nodes of the case tree that have no children.

- Absurd clauses may be omitted if removing the corresponding internal
  nodes from the case tree does not result in other internal nodes
  becoming childless.

- Non-absurd clauses may be replaced by catchall clauses if (1) the
  patterns of those catchall clauses are more general than the omitted
  clauses, (2) the added catchall clauses are not more general than
  any of the clauses that follow it, and (3) removing the leaves
  corresponding to the omitted clauses does not result in any internal
  nodes becoming childless.

As an example, consider the case tree for the definition of the
``lookup`` function defined above:

.. code-block:: agda

  lookup xs i = case xs of
    []       → case i of {}
    (x ∷ xs) → case i of
      zero    → x
      (suc i) → lookup xs i

The absurd clause arises from the case split on ``i`` in the branch
where ``xs = []``, which leads to zero cases. The two normal clauses
arise from the two leaves of the case tree. If the case ``[] → case i
of {}`` is removed from the case tree, all the remaining internal
nodes still have at least one child, hence the absurd clause may be
left out of the definition.

For a full formal description of the algorithm that Agda uses to
construct a case tree and check coverage of definitions by pattern
matching, refer to the article `Elaborating dependent (co)pattern
matching: No pattern left behind
<https://www.cambridge.org/core/journals/journal-of-functional-programming/article/elaborating-dependent-copattern-matching-no-pattern-left-behind/F13CECDAB2B6200135D45452CA44A8B3>`__.
