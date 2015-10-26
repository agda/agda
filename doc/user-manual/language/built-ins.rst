.. _built-ins:

*********
Built-ins
*********

.. note::
   This page is incomplete.

The Agda type checker knows about, and has special treatment for, a number of
different concepts. The most prominent is natural numbers, which has a special
representation as Haskell integers and support for fast arithmetic. The surface
syntax of these concepts are not fixed, however, so in order to use the special
treatment of natural numbers (say) you define an appropriate data type and then
bind that type to the natural number concept using a ``BUILTIN`` pragma.

Some built-in types support primitive functions that have no corresponding Agda
definition. These functions are declared using the ``primitive`` keyword by
giving their type signature. The primitive functions associated with each
built-in type are given below.

.. _built-in-nat:

Natural numbers
---------------

Built-in natural numbers are bound using the ``NATURAL`` built-in as follows::

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

The names of the data type and the constructors can be chosen freely, but the
shape of the datatype needs to match the one given above (modulo the order of
the constructors). Note that the constructors need not be bound explicitly.

Binding the built-in natural numbers as above has the following effects:

- The use of :ref:`natural number literals <lexical-structure-int-literals>` is
  enabled. By default the type of a natural number literal will be ``Nat``, but
  it can be :ref:`overloaded <literal-overloading>` to include other types as
  well.
- Closed natural numbers are represented as Haskell integers at compile-time.
- The compiler backends :ref:`compile natural numbers <compile-nat>` to the
  appropriate number type in the target language.
- Enabled binding the built-in natural number functions described below.

Functions on natural numbers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are a number of built-in functions on natural numbers. These are special
in that they have both an Agda definition and a primitive implementation. The
primitive implementation is used to evaluate applications to closed terms, and
the Agda definition is used otherwise. This lets you prove things about the
functions while still enjoying good performance of compile-time evaluation. The
built-in functions are the following::

  _+_ : Nat → Nat → Nat
  zero  + m = m
  suc n + m = suc (n + m)
  {-# BUILTIN NATPLUS _+_ #-}

  _-_ : Nat → Nat → Nat
  n     - zero  = n
  zero  - suc m = zero
  suc n - suc m = n - m
  {-# BUILTIN NATMINUS _-_ #-}

  _*_ : Nat → Nat → Nat
  zero  * m = zero
  suc n * m = n * m + m
  {-# BUILTIN NATTIMES _*_ #-}

  _==_ : Nat → Nat → Bool
  zero  == zero  = true
  suc n == suc m = n == m
  _     == _     = false
  {-# BUILTIN NATEQUALS _==_ #-}

  _<_ : Nat → Nat → Bool
  _     < zero  = false
  zero  < suc _ = true
  suc n < suc m = n < m
  {-# BUILTIN NATLESS _<_ #-}

  divAux : Nat → Nat → Nat → Nat → Nat
  divAux k m  zero    j      = k
  divAux k m (suc n)  zero   = divAux (suc k) m n m
  divAux k m (suc n) (suc j) = divAux k m n j
  {-# BUILTIN NATDIVSUCAUX divAux #-}

  modAux : Nat → Nat → Nat → Nat → Nat
  modAux k m  zero    j      = k
  modAux k m (suc n)  zero   = modAux 0 m n m
  modAux k m (suc n) (suc j) = modAux (suc k) m n j
  {-# BUILTIN NATMODSUCAUX modAux #-}

The Agda definitions are checked to make sure that they really define the
corresponding built-in function. The definitions are not required to be exactly
those given above, for instance, addition and multiplication can be defined by
recursion on either argument, and you can swap the arguments to the addition in
the recursive case of multiplication.

The ``NATDIVSUCAUX`` and ``NATMODSUCAUX`` are built-ins bind helper functions
for defining natural number division and modulo operations, and satisfy the
properties

::

  div n (suc m) ≡ divAux 0 m n m
  mod n (suc m) ≡ modAux 0 m n m

Integers
--------

.. warning::
   **The built-in integers will likely change in future versions of Agda.** The
   current version is not satisfactory since it is completely opaque to the
   type checker. This means that, unlike for natural numbers, you cannot prove
   properties about the primitive functions on integers.

Built-in integers are bound using the ``INTEGER`` built-in as follows::

  postulate Int : Set
  {-# BUILTIN INTEGER Int #-}

It supports the following primitive operations (given suitable bindings for
`Nat <Natural numbers_>`_, `Bool <Booleans_>`_ and `String <Strings_>`_) with
the obvious implementations::

  primitive
    primNatToInteger    : Nat → Int
    primIntegerMinus    : Int → Int → Int
    primIntegerPlus     : Int → Int → Int
    primIntegerTimes    : Int → Int → Int
    primIntegerEquality : Int → Int → Bool
    primIntegerLess     : Int → Int → Bool
    primIntegerAbs      : Int → Nat
    primNatToInteger    : Nat → Int
    primShowInteger     : Int → String

.. _built-in-float:

Floats
------

Floating point numbers are bound with the ``FLOAT`` built-in::

  postulate Float : Set
  {-# BUILTIN FLOAT Float #-}

This lets you use :ref:`floating point literals <lexical-structure-float-literals>`.
Floats are represented by the type checker as Haskell Doubles. The following
primitive functions are available (with suitable bindings for `Nat <Natural
numbers_>`_, `Bool <Booleans_>`_, `String <Strings_>`_ and `Int
<Integers_>`_)::

  primitive
    primNatToFloat    : Nat → Float
    primFloatPlus     : Float → Float → Float
    primFloatMinus    : Float → Float → Float
    primFloatTimes    : Float → Float → Float
    primFloatDiv      : Float → Float → Float
    primFloatEquality : Float → Float → Bool
    primFloatLess     : Float → Float → Bool
    primRound         : Float → Int
    primFloor         : Float → Int
    primCeiling       : Float → Int
    primExp           : Float → Float
    primLog           : Float → Float
    primSin           : Float → Float
    primShowFloat     : Float → String

These are implemented by the corresponding Haskell functions with a few
exceptions:

- ``primFloatEquality NaN NaN`` returns ``true``.
- ``primFloatLess`` sorts ``NaN`` below everything but negative infinity.
- ``primShowFloat`` returns ``"0.0"`` on negative zero.

This is to allow decidable equality and proof carrying comparisons on floating
point numbers.

Booleans
--------

Built-in booleans are bound using the ``BOOLEAN``, ``TRUE`` and ``FALSE`` built-ins::

  data Bool : Set where
    false true : Bool
  {-# BUILTIN BOOL  Bool  #-}
  {-# BUILTIN TRUE  true  #-}
  {-# BUILTIN FALSE false #-}

Note that unlike for natural numbers, you need to bind the constructors
separately. The reason for this is that Agda cannot tell which constructor
should correspond to true and which to false, since you are free to name them
whatever you like.

The only effect of binding the boolean type is that you can then use primitive
functions returning booleans, such as built-in ``NATEQUALS``.

Lists
-----

Built-in lists are bound using the ``LIST``, ``NIL`` and ``CONS`` built-ins::

  data List {a} (A : Set a) : Set a where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A
  {-# BUILTIN LIST List #-}
  {-# BUILTIN NIL  []   #-}
  {-# BUILTIN CONS _∷_  #-}

Even though Agda could easily tell which constructor is ``NIL`` and which is
``CONS`` you still have to bind them separately.

As with booleans, the only effect of binding the ``LIST`` built-in is to let
you use primitive functions working with lists, such as ``primStringToList``
and ``primStringFromList``.

.. _built-in-char:

Characters
----------

The character type is bound with the ``CHARACTER`` built-in::

  postulate Char : Set
  {-# BUILTIN CHARACTER Char #-}

Binding the character type lets you use :ref:`character literals
<lexical-structure-char-literals>`. The following primitive functions are
available on characters (given suitable bindings for `Bool <Booleans_>`_,
`Nat <Natural numbers_>`_ and `String <Strings_>`_)::

  primitive
    primIsLower    : Char → Bool
    primIsDigit    : Char → Bool
    primIsAlpha    : Char → Bool
    primIsSpace    : Char → Bool
    primIsAscii    : Char → Bool
    primIsLatin1   : Char → Bool
    primIsPrint    : Char → Bool
    primIsHexDigit : Char → Bool
    primToUpper    : Char → Char
    primToLower    : Char → Char
    primCharToNat  : Char → Nat
    primNatToChar  : Nat → Char
    primShowChar   : Char → String

These functions are implemented by the corresponding Haskell functions from
`Data.Char <data-char_>`_ (``ord`` and ``chr`` for ``primCharToNat`` and
``primNatToChar``). To make ``primNatToChar`` total ``chr`` is applied to the
natural number modulo ``0x110000``.

.. _data-char: https://hackage.haskell.org/package/base-4.8.1.0/docs/Data-Char.html

.. _built-in-string:

Strings
-------

The string type is bound with the ``STRING`` built-in::

  postulate String : Set
  {-# BUILTIN STRING String #-}

Binding the string type lets you use :ref:`string literals
<lexical-structure-string-literals>`. The following primitive functions are
available on strings (given suitable bindings for `Bool <Booleans_>`_, `Char
<Characters_>`_ and `List <Lists_>`_)::

  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowString     : String → String

Equality
--------

The identity typed can be bound to the built-in ``EQUALITY`` as follows::

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
  {-# BUILTIN EQUALITY _≡_  #-}
  {-# BUILTIN REFL     refl #-}

This lets you use proofs of type ``lhs ≡ rhs`` in the :ref:`rewrite
construction <with-rewrite>`.

primTrustMe
~~~~~~~~~~~

Binding the built-in equality type also enables the ``primTrustMe`` primitive::

  primitive
    primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

As can be seen from the type, ``primTrustMe`` must be used with the utmost care
to avoid inconsistencies.  What makes it different from a postulate is that if
``x`` and ``y`` are actually definitionally equal, ``primTrustMe`` reduces to
``refl``. One use of ``primTrustMe`` is to lift the primitive boolean equality
on built-in types like `String <Strings_>`_ to something that returns a proof
object::

  eqString : (a b : String) → Maybe (a ≡ b)
  eqString a b = if primStringEquality a b
                 then just primTrustMe
                 else nothing

With this definition ``eqString "foo" "foo"`` computes to ``just refl``.
Another use case is to erase computationally expensive equality proofs and
replace them by ``primTrustMe``::

  eraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
  eraseEquality _ = primTrustMe

Universe levels
---------------

Sized types
-----------

Coinduction
-----------

Reflection
----------

The reflection machinery has built-in types for representing Agda programs. See
:doc:`reflection` for a detailed description of these types.

