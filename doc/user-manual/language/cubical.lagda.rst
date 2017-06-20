..
  ::
  {-# OPTIONS --cubical #-}
  module language.cubical where

  open import Agda.Primitive
  open CubicalPrimitives renaming (primIMax to _∨_;
                                   primIMin to _∧_;
                                   primINeg to ~_)

  postulate Path : ∀ {a} {A : Set a} → A → A → Set a
  {-# BUILTIN PATH Path #-}

  postulate PathP : ∀ {a} → (A : I → Set a) → A i0 → A i1 → Set a
  {-# BUILTIN PATHP PathP #-}

.. _cubical:

***************************
Cubical Type Theory in Agda
***************************

Cubical Type Theory `Cohen et al., Cubical`_ is implemented in Agda (beta version).

To use cubical type theory, you need to run Agda with the ``--cubical`` command-line-option.
You can also write ``{-# OPTIONS --cubical #-}`` at the top of the file.

To define paths, use λ abstractions. For example, this is the definition of the constant path:

..
  ::
  module refl-example where

::

    refl : ∀ {a} {A : Set a} {x : A} → Path x x
    refl {x = x} = λ i → x

Although they use the same syntax, a path is not a function.
For example, the following is not valid:

.. code-block:: agda

  refl : ∀ {a} {A : Set a} {x : A} → Path x x
  refl {x = x} = λ (i : _) → x

-------------------------
The interval type (``I``)
-------------------------

The variable ``i`` in the definition of ``refl`` has type ``I``, which
topologically corresponds to the `real unit interval <https://en.wikipedia.org/wiki/Unit_interval>`_.
In a closed context, there are only two values of type ``I``: the two
ends of the interval, ``i0`` and ``i1``::

  a b : I
  a = i0
  b = i1

Elements of the interval form a `De Morgan algebra <https://en.wikipedia.org/wiki/De_Morgan_algebra>`_,
with minimum (``∧``), minimum (``∨``) and negation (``~``).

..
  ::
  module interval-example₁ (i j : I) where
    data _≡_ (i : I) : I → Set where
      reflI : i ≡ i

    infix 10 _≡_

    max min neg : I

::

    max = i ∨ j
    min = i ∧ j
    neg = ~ i

All the properties of de Morgan algebras hold definitionally. The ends
of the interval ``i0`` and ``i1`` are the bottom and top elements, respectively::

    p₁ : i0 ∨ i    ≡ i
    p₂ : i  ∨ i1   ≡ i1
    p₃ : i  ∨ j    ≡ j ∨ i
    p₄ : i  ∧ j    ≡ j ∧ i
    p₅ : ~ (~ i)   ≡ i
    p₆ : i0        ≡ ~ i1
    p₇ : ~ (i ∨ j) ≡ ~ i ∧ ~ j
    p₈ : ~ (i ∧ j) ≡ ~ i ∨ ~ j

..
    ::
    p₁ = reflI
    p₂ = reflI
    p₃ = reflI
    p₄ = reflI
    p₅ = reflI
    p₆ = reflI
    p₇ = reflI
    p₈ = reflI

----------
References
----------

.. _`Cohen et al., Cubical`:

   Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg; `“Cubical Type Theory: a constructive interpretation of the univalence axiom” <http://www.cse.chalmers.se/~simonhu/papers/cubicaltt.pdf>`_.

