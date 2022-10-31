
************
Cumulativity
************

Basics
------

Since version 2.6.2, Agda enables the use of strict (non-fibrant)
type universes ``SSet`` *(two-level type theory)* under the
``--two-level`` flag.

.. code-block:: agda

  {-# OPTIONS --two-level #-}

When the ``--two-level`` flag is enabled, Agda adds a new sort
``SSet`` of strict sets, i.e. types for which the identity type
satisfies the definitional K rule stating that any proof of
``x ≡ x`` is definitionally equal to ``refl``.

..
  ::

  module language.two-level where

  open import Agda.Primitive
  
.. code-block:: agda

  infix 4 _≡_
  data _≡_ {a} {A : SSet a} (x : A) : A → SSet a where
    refl : x ≡ x
