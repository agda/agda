..
  ::
  module language.pragmas where

.. _pragmas:

*******
Pragmas
*******

Pragmas are comments that are not ignored by Agda but have some
special meaning. The general format is:

.. code-block:: agda

  {-# <PRAGMA_NAME> <arguments> #-}

Index of pragmas
----------------

* :ref:`BUILTIN <built-ins>`

* :ref:`CATCHALL <case-trees>`

* :ref:`COMPILE <foreign-function-interface>`

* :ref:`FOREIGN <foreign-function-interface>`

* :ref:`NO_POSITIVITY_CHECK <no_positivity_check_pragma>`

* :ref:`NO_TERMINATION_CHECK <terminating_pragma>`

* :ref:`NON_TERMINATING <non_terminating_pragma>`

* :ref:`POLARITY <polarity_pragma>`

* :ref:`STATIC <built-ins>`

* :ref:`TERMINATING <terminating_pragma>`

* :ref:`INLINE <inline_pragma>`

* :ref:`NOINLINE <inline_pragma>`

* :ref:`WARNING_ON_USAGE <warning_pragma>`

* :ref:`WARNING_ON_IMPORT <warning_pragma>`

See also :ref:`command-line-pragmas`.

.. _inline_pragma:

The ``INLINE`` and ``NOINLINE`` pragmas
_______________________________________

A definition marked with an ``INLINE`` pragma is inlined during compilation. If it is a simple
definition that does no pattern matching, it is also inlined in function bodies at type-checking
time.

Definitions are automatically marked ``INLINE`` if they satisfy the following criteria:

* No pattern matching.
* Uses each argument at most once.
* Does not use all its arguments.

Automatic inlining can be prevented using the ``NOINLINE`` pragma.

Example::

  -- Would be auto-inlined since it doesn't use the type arguments.
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

  {-# NOINLINE _∘_ #-} -- prevents auto-inlining

  -- Would not be auto-inlined since it's using all its arguments
  _o_ : (Set → Set) → (Set → Set) → Set → Set
  (F o G) X = F (G X)

  {-# INLINE _o_ #-} -- force inlining


.. _warning_pragma:

The ``WARNING_ON_`` pragmas
___________________________

A library author can use a ``WARNING_ON_USAGE`` pragma to attach to a defined
name a warning to be raised whenever this name is used.

Similarly they can use a ``WARNING_ON_IMPORT`` pragma to attach to a module
a warning to be raised whenever this module is imported.

This would typically be used to declare a name or a module 'DEPRECATED' and
advise the end-user to port their code before the feature is dropped.

Users can turn these warnings off by using the ``--warn=noUserWarning`` option.
For more information about the warning machinery, see :ref:`warnings`.

Example::

  -- The new name for the identity
  id : {A : Set} → A → A
  id x = x

  -- The deprecated name
  λx→x = id

  -- The warning
  {-# WARNING_ON_USAGE λx→x "DEPRECATED: Use `id` instead of `λx→x`" #-}
  {-# WARNING_ON_IMPORT "DEPRECATED: Use module `Function.Identity` rather than `Identity`" #-}
