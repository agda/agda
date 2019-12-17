..
  ::
  module language.termination-checking where

      open import Agda.Builtin.Bool
      open import Agda.Builtin.Nat

.. _termination-checking:

********************
Termination Checking
********************

Not all recursive functions are permitted - Agda accepts only these recursive
schemas that it can mechanically prove terminating.

.. _termination-checking-primitive-recursion:

Primitive recursion
-------------------

In the simplest case, a given argument must be exactly one constructor
smaller in each recursive call.  We call this scheme primitive
recursion.  A few correct examples:

::

      plus : Nat → Nat → Nat
      plus zero    m = m
      plus (suc n) m = suc (plus n m)

      natEq : Nat → Nat → Bool
      natEq zero    zero    = true
      natEq zero    (suc m) = false
      natEq (suc n) zero    = false
      natEq (suc n) (suc m) = natEq n m

Both ``plus`` and ``natEq`` are defined by primitive recursion.

The recursive call in ``plus`` is OK because ``n`` is a subexpression
of ``suc n`` (so ``n`` is structurally smaller than ``suc n``).  So
every time plus is recursively called the first argument is getting
smaller and smaller.  Since a natural number can only have a finite
number of suc constructors we know that plus will always terminate.

``natEq`` terminates for the same reason, but in this case we can say
that both the first and second arguments of natEq are decreasing.

.. _termination-checking-structural-recursion:

Structural recursion
--------------------

Agda's termination checker allows more definitions than just primitive
recursive ones -- it allows structural recursion.

This means that we require recursive calls to be on a (strict)
subexpression of the argument (see ``fib`` below) - this is more
general that just taking away one constructor at a time.

::

      fib : Nat → Nat
      fib zero          = zero
      fib (suc zero)    = suc zero
      fib (suc (suc n)) = plus (fib n) (fib (suc n))

It also means that arguments may decrease in an lexicographic order -
this can be thought of as nested primitive recursion (see ``ack``
below).

::

      ack : Nat → Nat → Nat
      ack zero    m       = suc m
      ack (suc n) zero    = ack n (suc zero)
      ack (suc n) (suc m) = ack n (ack (suc n) m)

In ``ack`` either the first argument decreases or it stays the same and the second one decreases.
This is the same as a lexicographic ordering.

.. _termination-checking-with:

With-functions
--------------

Pragmas and Options
-------------------

.. _non_terminating-pragma:

* The ``NON_TERMINATING`` pragma

  This is a safer version of :ref:`TERMINATING <terminating-pragma>`
  which doesn't treat the affected functions as terminating. This
  means that ``NON_TERMINATING`` functions do not reduce during type
  checking. They do reduce at run-time and when invoking ``C-c C-n``
  at top-level (but not in a hole). The pragma was added in Agda
  2.4.2.

.. _terminating-pragma:

* The ``TERMINATING`` pragma

  Switches off termination checker for individual function definitions
  and mutual blocks and marks them as terminating. Since Agda 2.4.2.1
  replaced the ``NO_TERMINATION_CHECK`` pragma.

  The pragma must precede a function definition or a mutual block. The
  pragma cannot be used in :option:`--safe` mode.

  Examples:

  ..
    ::
      module single where

        postulate A : Set

  * Skipping a single definition: before type signature::

        {-# TERMINATING #-}
        a : A
        a = a

  * Skipping a single definition: before first clause::

        b : A
        {-# TERMINATING #-}
        b = b

  * Skipping an old-style mutual block: Before `mutual` keyword::

        {-# TERMINATING #-}
        mutual
          c : A
          c = d

          d : A
          d = c

  * Skipping an old-style mutual block: Somewhere within `mutual`
    block before a type signature or first function clause::

        mutual
         {-# TERMINATING #-}
         e : A
         e = f

         f : A
         f = e

  * Skipping a new-style mutual block: Anywhere before a type
    signature or first function clause in the block::

        g : A
        h : A

        g = h
        {-# TERMINATING #-}
        h = g

.. _termination-checking-references:

References
----------

`Andreas Abel, Foetus -- termination checker for simple functional programs
<http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.44.3494&rank=1>`_
