..
  ::
  module language.mixfix-operators where

  data Bool : Set where
    true  : Bool
    false : Bool

  data _≡_ {A : Set} : (a b : A) → Set where
    refl : {a : A} → a ≡ a

  infix 4 _≡_

.. _mixfix-operators:

****************
Mixfix Operators
****************

A name containing one or more name parts and one or more ``_`` can be used as an operator where the arguments go in place of the ``_``. For instance, an application of the name ``if_then_else_`` to arguments ``x``, ``y``, and ``z`` can be written either as a normal application ``if_then_else_ x y z`` or as an operator application ``if x then y else z``.

Examples:
::

  _and_ : Bool → Bool → Bool
  true and x = x
  false and _ = false

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y

  _⇒_   : Bool → Bool → Bool
  true  ⇒ b = b
  false ⇒ _ = true


Precedence
==========

Consider the expression ``true and false ⇒ false``.
Depending on which of ``_and_`` and ``_⇒_`` has more precedence,
it can either be read as ``(false and true) ⇒ false = true``,
or as ``false and (true ⇒ false) = true``.

Each operator is associated to a precedence, which is a floating point number
(can be negative and fractional!).
The default precedence for an operator is 20.

If we give ``_and_`` more precedence than ``_⇒_``, then we will get the first result::

  infix 30 _and_
  -- infix 20 _⇒_ (default)

  p-and : {x y z : Bool} →  x and y ⇒ z  ≡  (x and y) ⇒ z
  p-and = refl

  e-and : false and true ⇒ false  ≡  true
  e-and = refl

But, if we declare a new operator ``_and’_``
and give it less precedence than
``_⇒_``, then we will get the second result::

  _and’_ : Bool → Bool → Bool
  _and’_ = _and_
  infix 15 _and’_
  -- infix 20 _⇒_ (default)

  p-⇒ : {x y z : Bool} →  x and’ y ⇒ z  ≡  x and’ (y ⇒ z)
  p-⇒ = refl

  e-⇒ : false and’ true ⇒ false  ≡  false
  e-⇒ = refl


Associativity
=============

Consider the expression ``true ⇒ false ⇒ false``. Depending on whether ``_⇒_`` is
associates to the left or to the right, it can be read as
``(false ⇒ true) ⇒ false = false``, or ``false ⇒ (true ⇒ false) = true``,
respectively.

If we declare an operator ``_⇒_`` as ``infixr``, it will associate to the right::

  infixr 20 _⇒_

  p-right : {x y z : Bool} →  x ⇒ y ⇒ z  ≡  x ⇒ (y ⇒ z)
  p-right = refl

  e-right : false ⇒ true ⇒ false  ≡  true
  e-right = refl

If we declare an operator ``_⇒’_`` as ``infixl``, it will associate to the left::

  infixl 20 _⇒’_

  _⇒’_ : Bool → Bool → Bool
  _⇒’_ = _⇒_

  p-left : {x y z : Bool} →  x ⇒’ y ⇒’ z  ≡  (x ⇒’ y) ⇒’ z
  p-left = refl

  e-left : false ⇒’ true ⇒’ false  ≡  false
  e-left = refl


Ambiguity and Scope
===================

If you have not yet declared the fixity of an operator, Agda will
complain if you try to use ambiguously:

.. code-block:: agda

  e-ambiguous : Bool
  e-ambiguous = true ⇒ true ⇒ true

.. code-block:: none

  Could not parse the application true ⇒ true ⇒ true
  Operators used in the grammar:
    ⇒ (infix operator, level 20)


Fixity declarations may appear anywhere in a module that other
declarations may appear. They then apply to the entire scope in which
they appear (i.e. before and after, but not outside).
