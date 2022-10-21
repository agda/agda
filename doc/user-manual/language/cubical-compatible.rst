..
  ::
  {-# OPTIONS --guardedness #-}

  module language.cubical-compatible where

.. _cubical-compatible:

******************
Cubical compatible
******************

The option ``--cubical-compatible`` specifies whether the module being
type-checked is compatible with Cubical Agda: modules without this flag
can not be imported from ``--cubical`` modules.

.. note::
  Prior to Agda 2.6.3, the ``--cubical-compatible`` flag did not exist,
  and ``--without-K`` also implied the (internal) generation of Cubical
  Agda-specific code. See `#5843
  <https://github.com/agda/agda/issues/5843>` for the rationale behind
  this change.

Compatibility with Cubical Agda consists of:

- No reasoning principles incompatible with univalent type theory may be
  used. This behaviour is controlled by the the :ref:`without-K` flag,
  which ``--cubical-compatible`` implies.

- Due to specifics of the Cubical Agda implementation, several kinds of
  Agda definition need internal support code to be generated during their
  elaboration.

Occasionally, elaborator bugs can result in errors surfacing from these
internal definitions, despite the code being type-correct. To avoid
showing errors mentioning cubical definitions when the user-written code
is independent of Cubical Agda, these internal definitions are now gated
behind ``--cubical-compatible``.

The ``--cubical-compatible`` option is coinfective (see
:ref:`consistency-checking-options`): the generated support code for
functions may depend on those of importing modules.
