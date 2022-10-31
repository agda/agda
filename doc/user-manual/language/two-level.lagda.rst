
************
Strict Types
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
satisfies the definitional K rule.

..
  ::

  module language.two-level where

  open import Agda.Primitive
  
.. code-block:: agda

  infix 4 _≡ˢ_
  data _≡ˢ_ {a} {A : SSet a} (x : A) : A → SSet a where
    refl : x ≡ˢ x

The identity type of strict types are defined to be itself strict
types. It satisfies the K rule.

.. code-block:: agda

  K : {a} {A : SSet a} {x : A} (p : x ≡ˢ x) → p ≡ˢ refl
  K refl = refl

