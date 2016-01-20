.. _function-definitions:

********************
Function Definitions
********************

.. note::
   This is a stub.

Pattern matching
----------------

.. _dot-patterns:

Dot patterns
~~~~~~~~~~~~

.. _absurd-patterns:

Absurd patterns
~~~~~~~~~~~~~~~

Function declarations
---------------------

The general form for defining a function is
::

 f : (x1 : A1) → … → (xn : An) → B
 f p1 … pn = d
 …
 f q1 … qn = e

where ``f`` is a new identifier, ``A`` is a type, ``B`` is a type under the assumption that the variable ``x`` has the type ``A``, ``p_i`` and ``q_i`` are patterns and ``d`` and ``e`` are expressions.

The declaration above gives the identifier ``f`` the type ``(x1 : A1) → … → (xn : An) → B`` and ``f`` is defined by the defining equations. Patterns are matched from top to bottom, i.e., the first pattern that matches the actual parameters is the one that is used.

Abstraction
-----------
An object of type ``(x : A) → B`` is always equal to
::

 \x → b

where ``b : B`` under the assumption that ``x : A``.

Typed abstraction can also be used:
::

 \(x : A) → b

is another notation for the abstraction above if the type of the variable ``x`` is ``A``.

Application
-----------
The application of a function ``f : (x : A) → B`` to an argument ``a : A`` is written ``f a`` and the type of this is B[x := a].


Notational conventions
----------------------

Function types:
::

 (x : A)(y : B) → C    is the same as (x : A) → (y : B) → C
 (x y : A) → C         is the same as (x : A)(y : A) → C
 forall (x : A) → C    is the same as (x : A) → C
 forall x → C          is the same as (x : _) → C
 forall x y → C        is the same as forall x → forall y → C

You can also use the Unicode symbol ``∀`` (type “\all” in the Emacs Agda mode) instead of forall.

Functional abstraction:::

 \x y → e is the same as \x → (\y → e)

Functional application:::

 f a b is the same as (f a) b.

