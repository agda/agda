..
  ::
  module language.mixfix-operators where

  data Bool : Set where
    true  : Bool
    false : Bool

  module M where
    postulate _∙_ : Bool → Bool → Bool

.. _mixfix-operators:

****************
Mixfix Operators
****************

A type name, function name, or constructor name can comprise one or more name
parts if we separate them with underscore characters ``_``, and the
resulting name can be used as an operator. From left to right, each argument
goes in the place of each underscore ``_``.

For instance, we can join with underscores the name parts ``if``, ``then``,
and ``else`` into a single name ``if_then_else_``,
as in the following declaration::

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y

The application of the
function name ``if_then_else_`` to some arguments ``x``, ``y``, and ``z``
can be written as:

* a standard application by using the full name ``if_then_else_ x y z``

* an operator application by placing the arguments between the name parts
  ``if x then y else z``, leaving a space between arguments and part names

* other *sections* of the full name, for instance leaving one or two underscores:

  * ``(if_then y else z) x``
  * ``(if x then_else z) y``
  * ``if x then y else_ z``
  * ``if x then_else_ y z``
  * ``if_then y else_ x z``
  * ``(if_then_else z) x y``

Mixfix operators are not limited to functions, they are also allowed as names for types and constructors::

  -- Infix type operator _≡_
  data _≡_ {A : Set} : (a b : A) → Set where
    refl : {a : A} → a ≡ a

  -- Infix constructor  _∷_
  data List (A : Set) : Set where
    nil  : List A
    _∷_ : A → List A → List A

.. _precedence:

Precedence
==========

For the dicussion of precedence, assume the following operators::

  _and_ : Bool → Bool → Bool
  true  and x = x
  false and _ = false

  _⇒_   : Bool → Bool → Bool
  true  ⇒ b = b
  false ⇒ _ = true

Consider the expression ``false and true ⇒ false``.
Depending on which of ``_and_`` and ``_⇒_`` binds is given precendence,
it can either be read as ``(false and true) ⇒ false`` (which is ``true``),
or as ``false and (true ⇒ false)`` (which is ``false``).

Each operator is associated to a *precedence*, which is a floating point number
(can be negative and fractional!).
The default precedence for an operator is 20.

The type operator for constructing equalities is typically given a low precedence like 4::

  infix 4 _≡_

If we give ``_and_`` more precedence than ``_⇒_``, then we will get the first result::

  infix 30 _and_
  -- infix 20 _⇒_ (default)

  variable
    x y z : Bool

  p-and : x and y ⇒ z  ≡  (x and y) ⇒ z
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

  p-⇒ : x and’ y ⇒ z  ≡  x and’ (y ⇒ z)
  p-⇒ = refl

  e-⇒ : false and’ true ⇒ false  ≡  false
  e-⇒ = refl

Fixities can be changed when importing with a ``renaming`` directive::

  open M using (_∙_)
  open M renaming (_∙_ to infixl 10 _*_)

This code brings two instances of the operator ``_∙_`` in scope:

* the first named ``_∙_`` and with its original fixity
* the second named ``_*_`` and with the fixity changed to act like a
  left associative operator of precedence 10.

.. _associativity:

Associativity
=============

Consider the expression ``true ⇒ false ⇒ false``. Depending on whether ``_⇒_``
associates to the left or to the right, it can be read as
``(false ⇒ true) ⇒ false = false``, or ``false ⇒ (true ⇒ false) = true``,
respectively.

If we declare an operator ``_⇒_`` as ``infixr``, it will associate to the right::

  infixr 20 _⇒_

  p-right : x ⇒ y ⇒ z  ≡  x ⇒ (y ⇒ z)
  p-right = refl

  e-right : false ⇒ true ⇒ false  ≡  true
  e-right = refl

If we declare an operator ``_⇒’_`` as ``infixl``, it will associate to the left::

  infixl 20 _⇒’_

  _⇒’_ : Bool → Bool → Bool
  _⇒’_ = _⇒_

  p-left : x ⇒’ y ⇒’ z  ≡  (x ⇒’ y) ⇒’ z
  p-left = refl

  e-left : false ⇒’ true ⇒’ false  ≡  false
  e-left = refl

Closed, pre-, and postfix operators
===================================

An operator with only holes ``_`` in the interior is called closed,
e.g. ``[_]`` or ``begin_end`` or ``⟨_∣_⟩``.
Those need no fixity declaration.
Supplying one nevertheless will result in warning :option:`FixityDeclarationForNonOperator`.
This warning will also fire if you declare the fixity for a name that is not an operator at all, like ``infix 42 true``.

Generally, *precedences never apply to inner holes*.

Consequently, classification of operators into closed, pre-, post-, and infix operators only considers the holes at the extremities (start or end of the name).

1. Infix operators have holes on both sides, e.g. ``_⇒_`` and ``_and_`` but also ``_≡⟨_⟩_``.
   They may be left-, right-, or non-associative.

2. Prefix operators have a hole on the left, e.g. ``-_`` or ``if_then_else_``.
   They naturally always associate to the right.
   E.g. ``- - 5`` means ``- (- 5)``; the alternative ``(- -) 5`` would be nonsensical.

3. Postfix operators have a hole on the right, e.g. ``_!`` or ``_∎`` or ``_[_/_]``.
   They naturally always associate to the left.

4. Closed operators have neither.

Agda currently lacks specific precedence declarations for pre- and postfix operators and accepts any of ``infix``, ``infixl``, or ``infixr``, e.g. ``infix 6 -_`` works.

.. note::

  Even when precedence should not matter in the use of pre- and postfix operators,
  Agda rejects a term with incorrect precedences.
  E.g. ``4 + - 3`` is rejected unless ``_+_`` has a higher precedence than ``-_``.
  (See `Issue #1448 <https://github.com/agda/agda/issues/1448>`_.)


Ambiguity and Scope
===================

If you have not yet declared the fixity of an operator, Agda will
complain if you try to use it ambiguously:

.. code-block:: agda

  e-ambiguous : Bool
  e-ambiguous = true ⇒ true ⇒ true

.. code-block:: none

  Could not parse the application true ⇒ true ⇒ true
  Operators used in the grammar:
    ⇒ (infix operator, level 20)


Fixity declarations may appear anywhere in a module body.
They apply to the entire scope in which
they appear (i.e., before and after, but not outside).

Core operators
==============

Application (juxtaposition) and the function type constructor ``→``
are directly handled in the parser
and cannot be assigned precedence and associativity by the user.
However, we can understand them in the framework of operators as follows:

The function type constructor ``→`` is a right-associative operator with minimal precedence (-∞).
Any operator the user defines binds stronger than ``→``.

Application is a left-associative operator with maximal precedence (+∞).
It binds stronger than any user-defined operator.

Operators in telescopes
=======================

Agda does not yet support declaring the fixity of operators declared in
:ref:`telescopes<telescopes>`,
see `Issue #1235 <https://github.com/agda/agda/issues/1235>`_.

This can be worked around by aliasing the operator via a ``let``-binding,
which may include a fixity declaration::

  module _ {A : Set} (_+_ : A → A → A) (let infixl 5 _+_; _+_ = _+_) where
