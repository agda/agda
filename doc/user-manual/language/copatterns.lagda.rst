..
  ::
  module language.copatterns where

  data _≡_ {A : Set} : A → A →  Set where
    refl : {a : A} → a ≡ a

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  data Bool : Set where
    true false : Bool

  {-# BUILTIN NATURAL Nat #-}


.. _copatterns:

**********
Copatterns
**********

.. note:: If you are looking for information on how to use copatterns with
   coinductive records, please visit the section on :ref:`coinduction <coinduction>`.

Consider the following record::

  record Enumeration (A : Set) : Set where
    constructor enumeration
    field
      start    : A
      forward  : A → A
      backward : A → A


This gives an interface that allows us to move along the elements of a
data type ``A``.

For example, we can get the “third” element of a type ``A``:

..
  ::
  module _ where

::

    open Enumeration

    3rd : {A : Set} → Enumeration A → A
    3rd e = forward e (forward e (forward e (start e)))

Or we can go back 2 positions starting from a given ``a``:

::

  backward-2 : {A : Set} → Enumeration A → A → A
  backward-2 e a = backward (backward a)
    where
      open Enumeration e


Now, we want to use these methods on natural numbers. For this, we need
a record of type ``Enumeration Nat``. Without copatterns, we would
specify all the fields in a single expression:

..
  ::
  module Without-Copatterns where

::

    open Enumeration

    enum-Nat : Enumeration Nat
    enum-Nat = record
      { start    = 0
      ; forward  = suc
      ; backward = pred
      }
      where
        pred : Nat → Nat
        pred zero    = zero
        pred (suc x) = x

    test₁ : 3rd enum-Nat ≡ 3
    test₁ = refl

    test₂ : backward-2 enum-Nat 5 ≡ 3
    test₂ = refl

Note that if we want to use automated case-splitting and pattern
matching to implement one of the fields, we need to do so in a separate
definition.

With *copatterns*, we can define the fields of a record as separate declarations,
in the same way that we would give different cases for a function:

..
  ::
  module With-Copatterns where

::

    open Enumeration

    enum-Nat : Enumeration Nat
    start    enum-Nat = 0
    forward  enum-Nat n = suc n
    backward enum-Nat zero    = zero
    backward enum-Nat (suc n) = n

The resulting behaviour is the same in both cases:

::

    test₁ : 3rd enum-Nat ≡ 3
    test₁ = refl

    test₂ : backward-2 enum-Nat 5 ≡ 3
    test₂ = refl



Copatterns in function definitions
----------------------------------

In fact, we do not need to start at ``0``. We can allow the user to
specify the starting element.

Without copatterns, we just add the extra argument to the function declaration:

..
  ::
  module Without-Copatterns-2 where

::

    open Enumeration

    enum-Nat : Nat → Enumeration Nat
    enum-Nat initial = record
      { start    = initial
      ; forward  = suc
      ; backward = pred
      }
      where
        pred : Nat → Nat
        pred zero    = zero
        pred (suc x) = x

    test₁ : 3rd (enum-Nat 10) ≡ 13
    test₁ = refl

With copatterns, the function argument must be repeated once for each
field in the record:

..
  ::
  module With-Copatterns-2 where

::

    open Enumeration

    enum-Nat : Nat → Enumeration Nat
    start    (enum-Nat initial) = initial
    forward  (enum-Nat _) n = suc n
    backward (enum-Nat _) zero    = zero
    backward (enum-Nat _) (suc n) = n


Mixing patterns and co-patterns
-------------------------------

Instead of allowing an arbitrary value, we want to limit the user to
two choices: ``0`` or ``42``.

Without copatterns, we would need an auxiliary definition to choose which
value to start with based on the user-provided flag:

..
  ::
  module Without-Copatterns-3 where

::

    open Enumeration

    if_then_else_ : {A : Set} → Bool → A → A → A
    if true  then x else _ = x
    if false then _ else y = y

    enum-Nat : Bool → Enumeration Nat
    enum-Nat ahead = record
      { start    = if ahead then 42 else 0
      ; forward  = suc
      ; backward = pred
      }
      where
        pred : Nat → Nat
        pred zero    = zero
        pred (suc x) = x


With copatterns, we can do the case analysis directly by pattern matching:

..
  ::
  module With-Copatterns-3 where

::

    open Enumeration

    enum-Nat : Bool → Enumeration Nat
    start    (enum-Nat true)  = 42
    start    (enum-Nat false) = 0
    forward  (enum-Nat _) n = suc n
    backward (enum-Nat _) zero    = zero
    backward (enum-Nat _) (suc n) = n

..
  ::
  module Tip where

.. tip:: When using copatterns to define an element of a record type,
   the fields of the record must be in scope. In the examples above,
   we use ``open Enumeration`` to bring the fields of the record into
   scope.

   Consider the first example:

   .. code-block:: agda

      enum-Nat : Enumeration Nat
      start    enum-Nat = 0
      forward  enum-Nat n = suc n
      backward enum-Nat zero    = zero
      backward enum-Nat (suc n) = n

   If the fields of the ``Enumeration`` record are not in scope (in
   particular, the ``start`` field), then Agda will not be able to
   figure out what the first copattern means:

   .. code-block:: agda

      Could not parse the left-hand side start enum-Nat
      Operators used in the grammar:
      None
      when scope checking the left-hand side start enum-Nat in the
      definition of enum-Nat


   The solution is to open the record before using its fields:

   ..
     ::
     module Opened where

   ::

       open Enumeration

       enum-Nat : Enumeration Nat
       start    enum-Nat = 0
       forward  enum-Nat n = suc n
       backward enum-Nat zero    = zero
       backward enum-Nat (suc n) = n
