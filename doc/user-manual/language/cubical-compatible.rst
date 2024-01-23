..
  ::
  {-# OPTIONS --guardedness #-}

  module language.cubical-compatible where

.. _cubical-compatible:

******************
Cubical compatible
******************

The option :option:`--cubical-compatible` specifies whether the module being
type-checked is compatible with Cubical Agda: modules without this flag
can not be imported from :option:`--cubical` modules.

.. note::
  Prior to Agda 2.6.3, the :option:`--cubical-compatible` flag did not
  exist, and :option:`--without-K` also implied the (internal) generation of
  Cubical Agda-specific code. See `Agda issue #5843
  <https://github.com/agda/agda/issues/5843>`_ for the rationale
  behind this change.

Compatibility with Cubical Agda consists of:

- No reasoning principles incompatible with univalent type theory may
  be used. This behaviour is controlled by the :ref:`without-K`
  flag (:option:`--without-K`), which :option:`--cubical-compatible` implies.

- Due to specifics of the Cubical Agda implementation, several kinds of
  Agda definition need internal support code to be generated during their
  elaboration.

Occasionally, elaborator bugs can result in errors surfacing from these
internal definitions, despite the code being type-correct. To avoid
showing errors mentioning cubical definitions when the user-written code
is independent of Cubical Agda, these internal definitions are now gated
behind :option:`--cubical-compatible`.

Note that code that uses (only) :option:`--without-K` can not be imported
from code that uses :option:`--cubical`. Thus library developers are
encouraged to use :option:`--cubical-compatible` instead of :option:`--without-K`,
if possible.

Note also that Agda tends to be quite a bit faster if :option:`--without-K`
is used instead of :option:`--cubical-compatible`.

The :option:`--cubical-compatible` option is coinfective (see
:ref:`consistency-checking-options`): the generated support code for
functions may depend on those of importing modules.
