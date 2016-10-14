..
  ::
  module language.sized-types where

.. _sized-types:

***********
Sized Types
***********

.. note::
   This is a stub.

Sizes help the termination checker by tracking the depth of data structures
across definition boundaries.

The built-in combinators for sizes are described in :ref:`builtin_sized_types`.

..
  ::
    module coinduction-lang where

    open import Agda.Builtin.Size
    open import Data.Bool
    open import Relation.Binary.PropositionalEquality

-------------------------
Example: Finite languages
-------------------------

See `Traytel 2016`_.

Decidable languages can be represented as infinite trees. Each node has as many
children as the number of characters in the alphabet ``A``. Each path from the root
of the tree to a node determines a possible word in the language. Each node
has a boolean label, which is ``true`` if and only if the word corresponding
to that node is in the language. In particular, the root node of the tree
is labelled ``true`` if and only if the word belongs to the language.

These infinite trees can be represented as the following coinductive data-type:

::

    record Lang (i : Size) (A : Set) : Set where
      coinductive
      field
        ν : Bool
        δ : ∀{j : Size< i} → A → Lang j A

    open Lang

As we said before, given a language ``a : Lang A``, ``ν a ≡ true`` iff
``ε ∈ a``. On the other hand, the language ``δ a x : Lang A`` is the
`Brzozowski derivative`_ of a with respect to the character ``x``, that is,
``w ∈ δ a x`` iff ``xw ∈ a``.


With this data type, we can define some regular languages. The first one, the
empty language, contains no words; so all the nodes are labelled ``false``::

    ∅ : ∀ {i A}  → Lang i A
    ν ∅ = false
    δ ∅ _ = ∅

The second one is the language containing a single word; the empty word. The
root node is labelled ``true``, and all the others are labelled ``false``::

    ε : ∀ {i A} → Lang i A
    ν ε = true
    δ ε _ = ∅

To compute the union (or sum) of two languages, we do a point-wise ``or``
operation on the labels of their nodes:

::

    _+_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
    ν (a + b) = ν a ∨ ν b
    δ (a + b) x = δ a x + δ b x

    infixl 10 _+_

Now, lets define concatenation.
The base case (``ν``) is straightforward: ``ε ∈ a·b`` iff  ``ε ∈ a`` and ``ε ∈ b``.

For the derivative (``δ``), assume that we have a word ``w``, ``w ∈ δ (a · b)
x``. This means that ``w = αβ``, with ``α ∈ a`` and ``β ∈ b``.

We have to consider two cases:

 #. ``ε ∈ a``. Then, either:
    * ``α = ε``, and ``w = β = x · β’``, where ``β’ ∈ δ b x``.
    * ``α = xα’``, with ``α’ ∈ δ a x``.

 #. ``ε ∉ a``. Then, only the second case above is possible:
    * ``α = xα’``, with ``α’ ∈ δ a x``.

::

    _·_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
    ν (a · b) = ν a ∧ ν b
    δ (a · b) x = if ν a then δ a x · b + δ b x else δ a x · b

    infixl 20 _·_

Here is where sized types really shine. Without sized types, the termination
checker would not be able to recognize that ``_+_`` or ``if_then_else`` are not
inspecting the tree, which could render the definition non-productive. By contrast,
with sized types, we know that the ``a + b`` is defined to the same
depth as ``a`` and ``b`` are.

In a similar spirit, we can define the Kleene star::

    _* : ∀ {i A} → Lang i A → Lang i A
    ν (a *) = true
    δ (a *) x = δ a x · a *

    infixl 30 _*

Again, because the types tell us that _·_ preserves the size of its
inputs, we can have the recursive call to ``a *`` under a function
call to ``_·_``.

Testing
-------

First, we want to give a precise notion of membership in a language.
We consider a word as a ``List`` of characters.

..
  ::
    module SizedMembership where

      data List (i : Size) (A : Set) : Set where
        []  : List i A
        _∷_ : {j : Size< i} → A → List j A → List i A

      infixr 7 _∷_

::

      _∈_ : ∀ {i} {A} → List i A → Lang i A → Bool
      [] ∈ a = ν a
      (x ∷ w) ∈ a = w ∈ δ a x

..
  ::
    module UnsizedMembership where

      open import Data.List

Note how the size of the word we test for membership cannot be
larger than the depth to which the language tree is defined.

If we want to use regular, non-sized lists, we need to ask for the
language to have size ``ω``.

::

      _∈_ : ∀ {A} → List A → Lang ω A → Bool
      [] ∈ a = ν a
      (x ∷ w) ∈ a = w ∈ δ a x

Intuitively, ``ω`` is a ``Size`` larger than the size of any term
than one could possibly define in Agda.

Now, let's consider binary strings as words. First, we
define the languages containing a single word of length 1::

    ⟦_⟧ : ∀ {i} → Bool → Lang i Bool
    ν ⟦ _ ⟧    =  false

    δ ⟦ false ⟧ false = ε
    δ ⟦ true ⟧ true = ε
    δ ⟦ false ⟧ true = ∅
    δ ⟦ true ⟧ false = ∅

Now we can define the bip-bop language, consisting of strings of even
length starting with “true”, where each “true” is followed by “false”, and
viceversa.

::

    bip-bop = (⟦ true ⟧ · ⟦ false ⟧)*


We can now test words for membership in the language ``bip-bop``

..
  ::
    open SizedMembership

::

    test₁ : (true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []) ∈ bip-bop ≡ true
    test₁ = refl

    test₂ : (true ∷ false ∷ true ∷ false ∷ true ∷ []) ∈ bip-bop ≡ false
    test₂ = refl

    test₃ : (true ∷ true ∷ false ∷ []) ∈ bip-bop ≡ false
    test₃ = refl

.. _`Brzozowski derivative`: https://en.wikipedia.org/wiki/Brzozowski_derivative

----------
References
----------

.. _`Traytel 2016`:

   * `Formal Languages, Formally and Coinductively, Dmitriy Traytel, FSCD (2016) <https://www21.in.tum.de/~traytel/papers/fscd16-coind_lang/paper.pdf>`_.
