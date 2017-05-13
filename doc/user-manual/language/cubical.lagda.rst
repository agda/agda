..
  ::
  {-# OPTIONS --cubical #-}
  module language.cubical where

  open import Agda.Primitive
  open CubicalPrimitives

  postulate Path : ∀ {a} {A : Set a} → A → A → Set a
  {-# BUILTIN PATH Path #-}

  postulate PathP : ∀ {a} → (A : I → Set a) → A i0 → A i1 → Set a
  {-# BUILTIN PATHP PathP #-}

.. _cubical:

***************************
Cubical type theory in Agda
***************************

`Cubical Type Theory <http://www.cse.chalmers.se/~simonhu/papers/cubicaltt.pdf>`_ is implemented in Agda (beta version).

To use cubical type theory, you need to run Agda with the ``--cubical`` command-line-option.
You can also write ``{-# OPTIONS --cubical #-}`` at the top of the file.

To define paths, use λ abstractions. For example, this is the definition of the constant path:

::

  refl : ∀ {a} {A : Set a} {x : A} → Path x x
  refl {x = x} = \ i -> x

The variable ``i`` has type ``I``, which topologically corresponds to the
real unit interval. In a closed context, there are only two values of type
``I``: the two ends of the interval, ``i0`` and ``i1``::

  a b : I
  a = i0
  b = i1

Although they use the same syntax, a path is not a function.
For example, the following is not valid:

.. code-block:: agda

  refl : ∀ {a} {A : Set a} {x : A} → Path x x
  refl {x = x} = λ (i : I) → x

