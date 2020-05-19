..
  ::
  module language.universe-levels where

  open import Agda.Builtin.Unit

.. _universe-levels:

***************
Universe Levels
***************

.. _intro-universes:

..
  ::
  module Monomorphic where

Introduction to universes
-------------------------

Russell's paradox implies that the collection of all sets is not itself a set. Namely, if there were such a set ``U``, then one could form the subset ``A ⊆ U`` of all sets that do not contain themselves. Then we would have ``A ∈ A`` if and only if ``A ∉ A``, a contradiction.

For similar reasons, not every Agda type is a ``Set``. For example, we have

.. code-block:: agda

    Bool : Set
    Nat : Set

but not ``Set : Set``. However, it is often convenient for ``Set`` to have a type of its own, and so in Agda, it is given the type ``Set₁``:

.. code-block:: agda

    Set : Set₁

In many ways, expressions of type ``Set₁`` behave just like expressions of type ``Set``; for example, they can be used as types of other things. However, the elements of ``Set₁`` are potentially *larger*; when ``A : Set₁``, then ``A`` is sometimes called a **large set**. In turn, we have

.. code-block:: agda

    Set₁ : Set₂
    Set₂ : Set₃

and so on. A type whose elements are types is called a **universe**;
Agda provides an infinite number of universes ``Set``, ``Set₁``,
``Set₂``, ``Set₃``, ..., each of which is an element of the next
one. In fact, ``Set`` itself is just an abbreviation for
``Set₀``. The subscript ``n`` is called the **level** of the
universe ``Setₙ``.

A note on syntax: you can also write ``Set1``, ``Set2``, etc., instead
of ``Set₁``, ``Set₂``. To enter a subscript in the Emacs mode, type
"``\_1``".

Universe example
~~~~~~~~~~~~~~~~

So why are universes useful? Because sometimes it is necessary to
define, and prove theorems about, functions that operate not just on
sets but on large sets. In fact, most Agda users sooner or later
experience an error message where Agda complains that ``Set₁ !=
Set``. These errors usually mean that a small set was used where a
large one was expected, or vice versa.

For example, suppose you have defined the usual datatypes for lists and cartesian products:

::

    data List (A : Set) : Set where
      [] : List A
      _::_ : A → List A → List A

    data _×_ (A B : Set) : Set where
     _,_ : A → B → A × B

    infixr 5 _::_
    infixr 4 _,_
    infixr 2 _×_

Now suppose you would like to define an operator ``Prod`` that inputs
a list of ``n`` sets and takes their cartesian product, like this:

.. code-block:: agda

    Prod (A :: B :: C :: []) = A × B × C

There is only one small problem with this definition. The type of ``Prod`` should be

.. code-block:: agda

    Prod : List Set → Set

However, the definition of ``List A`` specified that ``A`` had to be a
``Set``. Therefore, ``List Set`` is not a valid type. The solution is
to define a special version of the ``List`` operator that works for
large sets:

::

    data List₁ (A : Set₁) : Set₁ where
      []   : List₁ A
      _::_ : A → List₁ A → List₁ A

With this, we can indeed define:

::

    Prod : List₁ Set → Set
    Prod []        = ⊤
    Prod (A :: As) = A × Prod As

.. _universe-polymorphism:


..
  ::
  module Polymorphic where

Universe polymorphism
---------------------

Although we were able to give a type to the ``Prod`` operator by
defining a special notion of large list, this quickly gets
tiresome. Sooner or later, we find that we require yet another list
type ``List₂``, and it doesn't stop there. Also every function on
lists (such as ``append``) must be re-defined, and every theorem about
such functions must be re-proved, for every possible level.

The solution to this problem is universe polymorphism. Agda provides a
special primitive type ``Level``, whose elements are possible levels
of universes. In fact, the notation for the ``n`` th universe,
``Setₙ``, is just an abbreviation for ``Set n``, where ``n :
Level`` is a level. We can use this to write a polymorphic ``List``
operator that works at any level. The library ``Agda.Primitive`` must
be imported to access the ``Level`` type. The definition then looks
like this:

::

    open import Agda.Primitive

    data List {n : Level} (A : Set n) : Set n where
      []   : List A
      _::_ : A → List A → List A

This new operator works at all levels; for example, we have

.. code-block:: agda

    List Nat : Set
    List Set : Set₁
    List Set₁ : Set₂

Level arithmetic
~~~~~~~~~~~~~~~~

Even though we don't have the number of levels specified, we know that
there is a lowest level ``lzero``, and for each level ``n``, there
exists some higher level ``lsuc n``; therefore, the set of levels is
infinite. In addition, we can also take the least upper bound ``n
⊔ m`` of two levels. In summary, the following (and only the
following) operations on levels are provided:

.. code-block:: agda

    lzero : Level
    lsuc  : (n : Level) → Level
    _⊔_   : (n m : Level) → Level

This is sufficient for most purposes; for example, we can define the
cartesian product of two types of arbitrary (and not necessarily
equal) levels like this:

::

    data _×_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
       _,_ : A → B → A × B

With this definition, we have, for example:

.. code-block:: agda

    Nat × Nat : Set
    Nat x Set : Set₁
    Set × Set : Set₁

``forall`` notation
~~~~~~~~~~~~~~~~~~~

From the fact that we write ``Set n``, it can always be inferred that
``n`` is a level. Therefore, when defining universe-polymorphic
functions, it is common to use the `∀` (or `forall`) notation. For
example, the type of the universe-polymorphic ``map`` operator on
lists can be written

.. code-block:: agda

    map : ∀ {n m} {A : Set n} {B : Set m} → (A → B) → List A → List B

which is equivalent to

.. code-block:: agda

    map : {n m : Level} {A : Set n} {B : Set m} → (A → B) → List A → List B

Expressions of kind ``Setω``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In a sense, universes were introduced to ensure that every Agda
expression has a type, including expressions such as ``Set``,
``Set₁``, etc. However, the introduction of universe polymorphism
inevitably breaks this property again, by creating some new terms that
have no type. Consider the polymorphic singleton set ``Unit n :
Setₙ``, defined by

::

    data Unit (n : Level) : Set n where
      <> : Unit n

It is well-typed, and has type

.. code-block:: agda

    Unit : (n : Level) → Set n

However, the type ``(n : Level) → Set n``, which is a valid Agda
expression, does not belong to any universe. Indeed, the expression
denotes a function mapping levels to universes, so if it had a type,
it should be something like ``Level → Universe``, where ``Universe``
is the collection of all universes. But since the elements of
``Universe`` are types, ``Universe`` is itself a universe, so we have
``Universe : Universe``. This leads to circularity and
inconsistency. In other words, just as we cannot have a set of all
sets, we also can't have a universe of all universes.

As a consequence, although the expression ``(n : Level) → Set n``
**is** a type, it does not **have** a type. It does, however, have a
"kind", which Agda calls ``Setω``. The expression ``Setω`` itself is a
valid Agda type but cannot appear as part of an Agda term.  For
example, the following definition is valid:

::

    largeType : Setω
    largeType = (n : Level) → Set n

As a counterexample which attempts to use ``Setω`` as part of a term,
consider trying to form the singleton list ``[ Unit ]``:

.. code-block:: agda

    badList : List ((n : Level) → Set n)
    badList = Unit :: []

This generates an error message stating that ``Setω`` is not of the
form ``Set _``. The problem is that ``List`` can only be applied to
types that are part of ``Set n`` for some ``n : Level``, but ``(n :
Level) → Set n`` belongs to ``Setω`` which is not of this form. The
only type constructor that can be applied to expressions of kind
``Setω`` is ``→``.

Pragmas and options
-------------------

.. _type-in-type:

* The option ``--type-in-type`` disables the checking of universe level
  consistency for the whole file.

.. _omega-in-omega:

* The option ``--omega-in-omega`` enables the typing rule ``Setω :
  Setω`` (thus making Agda inconsistent) but otherwise leaves universe
  checks intact.

.. _no_universe_check-pragma:

* The pragma ``{-# NO_UNIVERSE_CHECK #-}`` can be put in front of a
  data or record type to disable universe consistency checking
  locally.  Example:

  ::

    {-# NO_UNIVERSE_CHECK #-}
    data U : Set where
      el : Set → U

  This pragma applies only to the check that the universe level of the
  type of each constructor argument is less than or equal to the
  universe level of the datatype, not to any other checks.

  .. versionadded:: 2.6.0

The options ``--type-in-type`` and ``--omega-in-omega`` and the pragma
``{-# NO_UNIVERSE_CHECK #-}`` cannot be used with `--safe`.
