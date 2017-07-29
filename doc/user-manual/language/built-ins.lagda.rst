..
  ::
  {-# OPTIONS --rewriting #-}
  module language.built-ins where

  data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

  postulate String : Set
  {-# BUILTIN STRING String #-}

  data ⊥ : Set where

  record _×_ (A B : Set) : Set where
    constructor _,_
    field proj₁ : A
          proj₂ : B
  open _×_ public

.. _built-ins:

*********
Built-ins
*********

.. contents::
   :depth: 1
   :local:

The Agda type checker knows about, and has special treatment for, a number of
different concepts. The most prominent is natural numbers, which has a special
representation as Haskell integers and support for fast arithmetic. The surface
syntax of these concepts are not fixed, however, so in order to use the special
treatment of natural numbers (say) you define an appropriate data type and then
bind that type to the natural number concept using a ``BUILTIN`` pragma.

Some built-in types support primitive functions that have no corresponding Agda
definition. These functions are declared using the ``primitive`` keyword by
giving their type signature.

Using the built-in types
------------------------

While it is possible to define your own versions of the built-in types and bind
them using ``BUILTIN`` pragmas, it is recommended to use the definitions in the
``Agda.Builtin`` modules. These modules are installed when you install Agda and
so are always available. For instance, built-in natural numbers are defined in
``Agda.Builtin.Nat``. The `standard library <std-lib_>`_ and the agda-prelude_
reexport the definitions from these modules.

.. _agda-prelude: https://github.com/UlfNorell/agda-prelude
.. _std-lib: https://github.com/agda/agda-stdlib

.. _built-in-unit:

The unit type
-------------

.. code-block:: agda

  module Agda.Builtin.Unit

The unit type is bound to the built-in ``UNIT`` as follows::

  record ⊤ : Set where
  {-# BUILTIN UNIT ⊤ #-}

Agda needs to know about the unit type since some of the primitive operations
in the :ref:`reflected type checking monad <reflection-tc-monad>` return values
in the unit type.

.. _built-in-bool:

Booleans
--------

.. code-block:: agda

  module Agda.Builtin.Bool where

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

..
  ::
  infixl 1 if_then_else_
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else _ = x
  if false then _ else y = y


.. _built-in-nat:

Natural numbers
---------------

.. code-block:: agda

  module Agda.Builtin.Nat

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
  suc n * m = (n * m) + m
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

  div-helper : Nat → Nat → Nat → Nat → Nat
  div-helper k m  zero    j      = k
  div-helper k m (suc n)  zero   = div-helper (suc k) m n m
  div-helper k m (suc n) (suc j) = div-helper k m n j
  {-# BUILTIN NATDIVSUCAUX div-helper #-}

  mod-helper : Nat → Nat → Nat → Nat → Nat
  mod-helper k m  zero    j      = k
  mod-helper k m (suc n)  zero   = mod-helper 0 m n m
  mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j
  {-# BUILTIN NATMODSUCAUX mod-helper #-}

The Agda definitions are checked to make sure that they really define the
corresponding built-in function. The definitions are not required to be exactly
those given above, for instance, addition and multiplication can be defined by
recursion on either argument, and you can swap the arguments to the addition in
the recursive case of multiplication.

The ``NATDIVSUCAUX`` and ``NATMODSUCAUX`` are built-ins bind helper functions
for defining natural number division and modulo operations, and satisfy the
properties

.. code-block:: agda

  div n (suc m) ≡ div-helper 0 m n m
  mod n (suc m) ≡ mod-helper 0 m n m


.. _built-in-integer:

Integers
--------

.. code-block:: agda

  module Agda.Builtin.Int

Built-in integers are bound with the ``INTEGER`` built-in to a data type with
two constructors: one for positive and one for negative numbers. The built-ins
for the constructors are ``INTEGERPOS`` and ``INTEGERNEGSUC``.

::

  data Int : Set where
    pos    : Nat → Int
    negsuc : Nat → Int
  {-# BUILTIN INTEGER       Int    #-}
  {-# BUILTIN INTEGERPOS    pos    #-}
  {-# BUILTIN INTEGERNEGSUC negsuc #-}

Here ``negsuc n`` represents the integer ``-n - 1``. Unlike for natural
numbers, there is no special representation of integers at compile-time since
the overhead of using the data type compared to Haskell integers is not that
big.

Built-in integers support the following primitive operation (given a
suitable binding for :ref:`String <built-in-string>`)::

  primitive
    primShowInteger : Int → String

.. _built-in-float:

Floats
------

.. code-block:: agda

  module Agda.Builtin.Float

Floating point numbers are bound with the ``FLOAT`` built-in::

  postulate Float : Set
  {-# BUILTIN FLOAT Float #-}

This lets you use :ref:`floating point literals
<lexical-structure-float-literals>`.  Floats are represented by the
type checker as IEEE 754 binary64 double precision floats, with the
restriction that there is exactly one NaN value. The following
primitive functions are available (with suitable bindings for
:ref:`Nat <built-in-nat>`, :ref:`Bool <built-in-bool>`,
:ref:`String <built-in-string>` and :ref:`Int <built-in-integer>`)::

  primitive
    primNatToFloat             : Nat → Float
    primFloatPlus              : Float → Float → Float
    primFloatMinus             : Float → Float → Float
    primFloatTimes             : Float → Float → Float
    primFloatNegate            : Float → Float
    primFloatDiv               : Float → Float → Float
    primFloatEquality          : Float → Float → Bool
    primFloatNumericalEquality : Float → Float → Bool
    primFloatNumericalLess     : Float → Float → Bool
    primRound                  : Float → Int
    primFloor                  : Float → Int
    primCeiling                : Float → Int
    primExp                    : Float → Float
    primLog                    : Float → Float
    primSin                    : Float → Float
    primCos                    : Float → Float
    primTan                    : Float → Float
    primASin                   : Float → Float
    primACos                   : Float → Float
    primATan                   : Float → Float
    primATan2                  : Float → Float → Float
    primShowFloat              : Float → String

The ``primFloatEquality`` primitive is intended to be used for decidable
propositional equality. To enable proof carrying comparisons while preserving
consisteny, the following laws apply:

- ``primFloatEquality NaN NaN`` returns ``true``.
- ``primFloatEquality NaN (primFloatNegate NaN)`` returns ``true``.
- ``primFloatEquality 0.0 -0.0`` returns ``false``.


For numerical comparisons, use the ``primFloatNumericalEquality`` and
``primFloatNumericalLess`` primitives. These are implemented by the
corresponding Haskell functions with the following behaviour and
exceptions:

- ``primFloatNumericalEquality 0.0 -0.0`` returns ``true``.
- ``primFloatNumericalEquality NaN NaN`` returns ``false``.
- ``primFloatNumericalLess NaN NaN`` returns ``false``.
- ``primFloatNumericalLess (primFloatNegate NaN) (primFloatNegate NaN)`` returns ``false``.
- ``primFloatNumericalLess NaN (primFloatNegate NaN)`` returns ``false``.
- ``primFloatNumericalLess (primFloatNegate NaN) NaN`` returns ``false``.
- ``primFloatNumericalLess`` sorts ``NaN`` below everything but negative infinity.
- ``primFloatNumericalLess -0.0 0.0`` returns ``false``.

.. warning::

   Do not use ``primFloatNumericalEquality`` to establish decidable
   propositional equality. Doing so makes Agda inconsistent, see
   Issue `#2169 <https://github.com/agda/agda/issues/2169>`_.

.. _built-in-list:

Lists
-----

.. code-block:: agda

  module Agda.Builtin.List

Built-in lists are bound using the ``LIST``, ``NIL`` and ``CONS`` built-ins::

  data List {a} (A : Set a) : Set a where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A
  {-# BUILTIN LIST List #-}
  {-# BUILTIN NIL  []   #-}
  {-# BUILTIN CONS _∷_  #-}
  infixr 5 _∷_

Even though Agda could easily tell which constructor is ``NIL`` and which is
``CONS`` you still have to bind them separately.

As with booleans, the only effect of binding the ``LIST`` built-in is to let
you use primitive functions working with lists, such as ``primStringToList``
and ``primStringFromList``.

..
  ::
  -- common functions on lists used in other files for examples
  _++_ : ∀ {a} {A : Set a} → List A → List A → List A
  [] ++ ys       = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  [_] : ∀ {a} {A : Set a} → A → List A
  [ x ] = x ∷ []


.. _built-in-char:

Characters
----------

.. code-block:: agda

  module Agda.Builtin.Char

The character type is bound with the ``CHARACTER`` built-in::

  postulate Char : Set
  {-# BUILTIN CHAR Char #-}

Binding the character type lets you use :ref:`character literals
<lexical-structure-char-literals>`. The following primitive functions
are available on characters (given suitable bindings for
:ref:`Bool <built-in-bool>`, :ref:`Nat <built-in-nat>` and
:ref:`String <built-in-string>`)::

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

.. code-block:: agda

  module Agda.Builtin.String

The string type is bound with the ``STRING`` built-in:

.. code-block:: agda

  postulate String : Set
  {-# BUILTIN STRING String #-}

Binding the string type lets you use :ref:`string literals
<lexical-structure-string-literals>`. The following primitive
functions are available on strings (given suitable bindings for
:ref:`Bool <built-in-bool>`, :ref:`Char <built-in-char>` and
:ref:`List <built-in-list>`)::

  postulate primStringToList   : String → List Char
  postulate primStringFromList : List Char → String
  postulate primStringAppend   : String → String → String
  postulate primStringEquality : String → String → Bool
  postulate primShowString     : String → String

String literals can be :ref:`overloaded <overloaded-strings>`.

.. _built-in-equality:

Equality
--------

.. code-block:: agda

  module Agda.Builtin.Equality

The identity type can be bound to the built-in ``EQUALITY`` as follows::

  infix 4 _≡_
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
  {-# BUILTIN EQUALITY _≡_  #-}

This lets you use proofs of type ``lhs ≡ rhs`` in the :ref:`rewrite
construction <with-rewrite>`.

Other variants of the identity type are also accepted as built-in:

.. code-block:: agda

  data _≡_ {A : Set} : (x y : A) → Set where
    refl : (x : A) → x ≡ x

The type of ``primTrustMe`` has to match the flavor of identity type.

primTrustMe
~~~~~~~~~~~

.. code-block:: agda

  module Agda.Builtin.TrustMe

Binding the built-in equality type also enables the ``primTrustMe`` primitive::

  primitive
    primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

As can be seen from the type, ``primTrustMe`` must be used with the
utmost care to avoid inconsistencies.  What makes it different from a
postulate is that if ``x`` and ``y`` are actually definitionally
equal, ``primTrustMe`` reduces to ``refl``. One use of ``primTrustMe``
is to lift the primitive boolean equality on built-in types like
:ref:`String <built-in-string>` to something that returns a proof
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

.. code-block:: agda

  module Agda.Primitive

:ref:`Universe levels <universe-levels>` are also declared using ``BUILTIN``
pragmas. In contrast to the ``Agda.Builtin`` modules, the ``Agda.Primitive`` module
is auto-imported and thus it is not possible to change the level built-ins. For
reference these are the bindings::

  postulate
    Level : Set
    lzero : Level
    lsuc  : Level → Level
    _⊔_   : Level → Level → Level

..
  This code cannot be typechecked because the identifiers are already bound
  in Agda.Primitive and are auto-imported.

.. code-block:: agda

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsuc  #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}

.. _builtin_sized_types:

Sized types
-----------

.. code-block:: agda

  module Agda.Builtin.Size

The built-ins for :ref:`sized types <sized-types>` are different from other
built-ins in that the names are defined by the ``BUILTIN`` pragma. Hence, to
bind the size primitives it is enough to write::

  {-# BUILTIN SIZEUNIV SizeUniv #-}  --  SizeUniv : SizeUniv
  {-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
  {-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
  {-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
  {-# BUILTIN SIZEINF   ω       #-}  --  ω        : Size
  {-# BUILTIN SIZEMAX  _⊔ˢ_     #-}  --  _⊔ˢ_     : Size → Size → Size

Coinduction
-----------

.. code-block:: agda

  module Agda.Builtin.Coinduction

The following built-ins are used for coinductive definitions::

  postulate
    ∞  : ∀ {a} (A : Set a) → Set a
    ♯_ : ∀ {a} {A : Set a} → A → ∞ A
    ♭  : ∀ {a} {A : Set a} → ∞ A → A
  {-# BUILTIN INFINITY ∞  #-}
  {-# BUILTIN SHARP    ♯_ #-}
  {-# BUILTIN FLAT     ♭  #-}

See :ref:`coinduction` for more information.

IO
--

.. code-block:: agda

  module Agda.Builtin.IO

The sole purpose of binding the built-in ``IO`` type is to let Agda check that
the ``main`` function has the right type (see :ref:`compilers`).

::

  postulate IO : Set → Set
  {-# BUILTIN IO IO #-}

Literal overloading
-------------------

.. code-block:: agda

  module Agda.Builtin.FromNat
  module Agda.Builtin.FromNeg
  module Agda.Builtin.FromString

The machinery for :ref:`overloading literals <literal-overloading>` uses
built-ins for the conversion functions.

Reflection
----------

.. code-block:: agda

  module Agda.Builtin.Reflection

The reflection machinery has built-in types for representing Agda programs. See
:doc:`reflection` for a detailed description.

Rewriting
---------

The experimental and totally unsafe :doc:`rewriting machinery <rewriting>` (not
to be confused with the :ref:`rewrite construct <with-rewrite>`) has a built-in
``REWRITE`` for the rewriting relation::

  postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set a
  {-# BUILTIN REWRITE _↦_ #-}

There is no ``Agda.Builtin`` module for the rewrite relation since different
rewriting experiments typically want different relations.

Static values
-------------

The ``STATIC`` pragma can be used to mark definitions which should
be normalised before compilation. The typical use case for this is
to mark the interpreter of an embedded language as ``STATIC``:

.. code-block:: agda

   {-# STATIC <Name> #-}

Strictness
----------

.. code-block:: agda

  module Agda.Builtin.Strict

There are two primitives for controlling evaluation order::

  primitive
    primForce      : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
    primForceLemma : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → primForce x f ≡ f x

where ``_≡_`` is the :ref:`built-in equality <built-in-equality>`. At compile-time
``primForce x f`` evaluates to ``f x`` when ``x`` is in weak head normal form (whnf),
i.e. one of the following:

  - a constructor application
  - a literal
  - a lambda abstraction
  - a type constructor application (data or record type)
  - a function type
  - a universe (``Set _``)

Similarly ``primForceLemma x f``, which lets you reason about programs using
``primForce``, evaluates to ``refl`` when ``x`` is in whnf.  At run-time,
``primForce e f`` is compiled (by the GHC :ref:`backend <compilers>`)
to ``let x = e in seq x (f x)``.

For example, consider the following function::

  -- pow’ n a = a 2ⁿ
  pow’ : Nat → Nat → Nat
  pow’ zero    a = a
  pow’ (suc n) a = pow’ n (a + a)

At compile-time this will be exponential, due to call-by-name evaluation, and
at run-time there is a space leak caused by unevaluated ``a + a`` thunks. Both
problems can be fixed with ``primForce``::

  infixr 0 _$!_
  _$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
  f $! x = primForce x f

  -- pow n a = a 2ⁿ
  pow : Nat → Nat → Nat
  pow zero    a = a
  pow (suc n) a =  pow n $! a + a
