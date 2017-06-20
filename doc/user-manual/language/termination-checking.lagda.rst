..
  ::
  module language.termination-checking where

.. _termination-checking:

********************
Termination Checking
********************

.. note::
   This is a stub.

.. _termination-checking-with:

With-functions
--------------

Pragmas and Options
-------------------

.. _non_terminating_pragma:

* The ``NON_TERMINATING`` pragma

  This is a safer version of :ref:`TERMINATING <terminating_pragma>`
  which doesn't treat the affected functions as terminating. This
  means that ``NON_TERMINATING`` functions do not reduce during type
  checking. They do reduce at run-time and when invoking ``C-c C-n``
  at top-level (but not in a hole). The pragma was added in Agda
  2.4.2.

.. _terminating_pragma:

* The ``TERMINATING`` pragma

  Switches off termination checker for individual function definitions
  and mutual blocks and marks them as terminating. Since Agda 2.4.2.1
  replaced the ``NO_TERMINATION_CHECK`` pragma.

  The pragma must precede a function definition or a mutual block. The
  pragma cannot be used in ``--safe`` mode.

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
