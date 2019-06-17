..
  ::
  module language.pattern-synonyms where

.. _pattern-synonyms:

****************
Pattern Synonyms
****************

A **pattern synonym** is a declaration that can be used on the left hand
side (when pattern matching) as well as the right hand side (in
expressions). For example::

    data Nat : Set where
      zero : Nat
      suc  : Nat → Nat

    pattern z    = zero
    pattern ss x = suc (suc x)

    f : Nat → Nat
    f z       = z
    f (suc z) = ss z
    f (ss n)  = n

Pattern synonyms are implemented by substitution on the abstract
syntax, so definitions are scope-checked but *not type-checked*. They
are particularly useful for universe constructions.

Overloading
-----------

Pattern synonyms can be overloaded as long as all candidates have the same
*shape*. Two pattern synonym definitions have the same shape if they are equal
up to variable and constructor names. Shapes are checked at resolution time and
after expansion of nested pattern synonyms.

For example::

    data List (A : Set) : Set where
      lnil  : List A
      lcons : A → List A → List A

    data Vec (A : Set) : Nat → Set where
      vnil  : Vec A zero
      vcons : ∀ {n} → A → Vec A n → Vec A (suc n)

    pattern [] = lnil
    pattern [] = vnil

    pattern _∷_ x xs = lcons x xs
    pattern _∷_ y ys = vcons y ys

    lmap : ∀ {A B} → (A → B) → List A → List B
    lmap f []       = []
    lmap f (x ∷ xs) = f x ∷ lmap f xs

    vmap : ∀ {A B n} → (A → B) → Vec A n → Vec B n
    vmap f []       = []
    vmap f (x ∷ xs) = f x ∷ vmap f xs

Flipping the arguments in the synonym for ``vcons``, changing it to ``pattern
_∷_ ys y = vcons y ys``, results in the following error when trying to use the
synonym:

.. code-block:: text

    Cannot resolve overloaded pattern synonym _∷_, since candidates
    have different shapes:
      pattern _∷_ x xs = lcons x xs
        at pattern-synonyms.lagda.rst:51,13-16
      pattern _∷_ ys y = vcons y ys
        at pattern-synonyms.lagda.rst:52,13-16
    (hint: overloaded pattern synonyms must be equal up to variable and
    constructor names)
    when checking that the clause lmap f (x ∷ xs) = f x ∷ lmap f xs has
    type {A B : Set} → (A → B) → List A → List B


Refolding
---------

For each pattern ``pattern lhs = rhs``, Agda declares a ``DISPLAY``
pragma refolding ``rhs`` to ``lhs`` (see :ref:`display_pragma` for
more details).
