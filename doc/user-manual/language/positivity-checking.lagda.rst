..
  ::
  module language.positivity-checking where

.. _positivity-checking:

*******************
Positivity Checking
*******************

.. note::
   This is a stub.

.. _no_positivity_check-pragma:

The ``NO_POSITIVITY_CHECK`` pragma
__________________________________

..
  ::
  module no-positivity-check-pragma where

The pragma switches off the positivity checker for data/record
definitions and mutual blocks. This pragma was added in Agda 2.5.1

The pragma must precede a data/record definition or a mutual
block. The pragma cannot be used in :option:`--safe` mode.

Examples:

..
  ::
    module single where

* Skipping a single data definition::

      {-# NO_POSITIVITY_CHECK #-}
      data D : Set where
        lam : (D → D) → D

* Skipping a single record definition::

      {-# NO_POSITIVITY_CHECK #-}
      record U : Set where
        field ap : U → U

..
  ::
    module old-style-record where

* Skipping an old-style mutual block. Somewhere within a mutual block
  before a data/record definition::

      mutual
        data D : Set where
          lam : (D → D) → D

        {-# NO_POSITIVITY_CHECK #-}
        record U : Set where
          field ap : U → U

..
  ::
    module old-style-mutual where

* Skipping an old-style mutual block. Before the ``mutual`` keyword::

      {-# NO_POSITIVITY_CHECK #-}
      mutual
        data D : Set where
          lam : (D → D) → D

        record U : Set where
          field ap : U → U

..
  ::
    module new-style-mutual where

* Skipping a new-style mutual block. Anywhere before the declaration
  or the definition of a data/record in the block::

      record U : Set
      data D   : Set

      record U where
        field ap : U → U

      {-# NO_POSITIVITY_CHECK #-}
      data D where
        lam : (D → D) → D

.. _polarity-pragma:

`POLARITY` pragmas
__________________

..
  ::
  module polarity-pragmas where

Polarity pragmas can be attached to postulates. The polarities express
how the postulate's arguments are used. The following polarities
are available:

* ``_``:  Unused.
* ``++``: Strictly positive.
* ``+``:  Positive.
* ``-``:  Negative.
* ``*``:  Unknown/mixed.

Polarity pragmas have the form ``{-# POLARITY name <zero or more
polarities> #-}``, and can be given wherever fixity declarations can
be given. The listed polarities apply to the given postulate's
arguments (explicit/implicit/instance), from left to right. Polarities
currently cannot be given for module parameters. If the postulate
takes n arguments (excluding module parameters), then the number of
polarities given must be between 0 and n (inclusive).

Polarity pragmas make it possible to use postulated type formers in
recursive types in the following way:
::

    postulate
      ∥_∥ : Set → Set

    {-# POLARITY ∥_∥ ++ #-}

    data D : Set where
      c : ∥ D ∥ → D

..
  ::
  module proof-of-bottom where

Note that one can use postulates that may seem benign, together with
polarity pragmas, to prove that the empty type is inhabited::

    postulate
      _⇒_    : Set → Set → Set
      lambda : {A B : Set} → (A → B) → A ⇒ B
      apply  : {A B : Set} → A ⇒ B → A → B

    {-# POLARITY _⇒_ ++ #-}

    data ⊥ : Set where

    data D : Set where
      c : D ⇒ ⊥ → D

    not-inhabited : D → ⊥
    not-inhabited (c f) = apply f (c f)

    d : D
    d = c (lambda not-inhabited)

    bad : ⊥
    bad = not-inhabited d

Polarity pragmas are not allowed in safe mode.
