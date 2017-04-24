..
  ::
  module language.record-types where

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat hiding (_==_; _<_)
  open import Agda.Builtin.List

  _||_ : Bool → Bool → Bool
  true  || x = true
  false || x = x

.. _record-types:

************
Record Types
************

Records are types for grouping values together. They generalise the
dependent product type by providing named fields and (optional)
further components.

Record types can be declared using the ``record`` keyword

..
  ::
  module Hide where

::

   record Pair (A B : Set) : Set where
     field
       fst : A
       snd : B

This defines a new type ``Pair : Set → Set → Set`` and two projection
functions

.. code-block:: agda

  Pair.fst : {A B : Set} → Pair A B → A
  Pair.snd : {A B : Set} → Pair A B → B

Elements of record types can be defined using a record expression

::

   p23 : Pair Nat Nat
   p23 = record { fst = 2; snd = 3 }

or using :ref:`copatterns <copatterns>`

::

   p34 : Pair Nat Nat
   Pair.fst p34 = 3
   Pair.snd p34 = 4

If you use the ``constructor`` keyword, you can also use the named
constructor to define elements of the record type:

::

  record Pair (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  p45 : Pair Nat Nat
  p45 = 4 , 5


In this sense, record types behave much like single constructor
datatypes (but see :ref:`eta-expansion` below).

.. _record-declarations:

Declaring, constructing and decomposing records
-----------------------------------------------

Declarating record types
~~~~~~~~~~~~~~~~~~~~~~~~

The general form of a record declaration is as follows:

.. code-block:: agda

   record <recordname> <parameters> : Set <level> where
     <directives>
     constructor <operator>
     field
       <fieldname1> : <type1>
       <fieldname2> : <type2>
       -- ...
     <declarations>

All the components are optional, and can be given in any order. In
particular, fields can be given in more than one block, interspersed
with other declarations.

Each field is a component of the record. Types of later fields can
depend on earlier fields.

The directives available are ``eta-equality``, ``no-eta-equality``
(see :ref:`eta-expansion`), ``inductive`` and ``co-inductive`` (see
:ref:`recursive-records`).

Constructing record values
~~~~~~~~~~~~~~~~~~~~~~~~~~

Record values are constructed by giving a value for each record field:

.. code-block:: agda

   record { <fieldname1> = <term1> ; <fieldname2> = <term2> ; ... }

where the types of the terms matches the types of the fields. If a
constructor ``<operator>`` has been declared for the record, this can
also be written

.. code-block:: agda

   <operator> <term1> <term2> ...

For named definitions, this can also be expressed using copatterns:

.. code-block:: agda

   <named-def> : <recordname> <parameters>
   <recordname>.<fieldname1> <named-def> = <term1>
   <recordname>.<fieldname2> <named-def> = <term2>
   ...


Building records from modules and record update
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``record { <fields> }`` syntax also accept module names. Fields
are defined using the corresponding definitions from the given module.
For instance assuming this record type R and module M:

.. code-block:: agda

   record R : Set where
     field
       x : X
       y : Y
       z : Z

   module M where
      x = ...
      y = ...

   r : R
   r = record { M; z = ... }

This construction supports any combination of explicit field
definitions and applied modules. If a field is both given explicitly
and available in one of the modules, then the explicit one takes
precedence. If a field is available in more than one module then this
is ambiguous and therefore rejected. As a consequence the order of
assignments does not matter.

The modules can be both applied to arguments and have import
directives such as hiding, using, and renaming. Here is a contrived
example building on the example above:

.. code-block:: agda

   module M2 (a : A) where
     w = ...
     z = ...

   r2 : A → R
   r2 a = record { M hiding (y); M2 a renaming (w to y) }

In particular, together with the fact that :ref:`all records define a module <record-modules>`, this can be used to "update" a record:

.. code-block:: agda

   r3 : R -- keeps all field values of r except for y
   r3 = record { R r; y = ... }

Decomposing record values
~~~~~~~~~~~~~~~~~~~~~~~~~

With the field name, we can project the corresponding component out of
a record value. It is also possible to pattern match against inductive
records:

::

  sum : Pair Nat Nat → Nat
  sum (x , y) = x + y

Internally, this is translated to

::

  sum' : Pair Nat Nat → Nat
  sum' p = (Pair.fst p) + (Pair.snd p)


.. note::
   Naming the constructor is not required to enable pattern matching against
   record values. Record expressions can appear as patterns.


.. _record-modules:

Record modules
--------------

Along with a new type, a record declaration also defines a module containing
the projection functions. This allows records to be "opened", bringing the
fields into scope. For instance

::

  swap : {A B : Set} → Pair A B → Pair B A
  swap p = snd , fst
    where open Pair p

It possible to add arbitrary definitions to the record module, by defining them
inside the record declaration

::

  record Functor (F : Set → Set) : Set₁ where
    field
      fmap : ∀ {A B} → (A → B) → F A → F B

    _<$_ : ∀ {A B} → A → F B → F A
    x <$ fb = fmap (λ _ → x) fb

.. note::
   In general new definitions need to appear after the field declarations, but
   simple non-recursive function definitions without pattern matching can be
   interleaved with the fields. The reason for this restriction is that the
   type of the record constructor needs to be expressible using :ref:`let-expressions`.
   In the example below ``D₁`` can only contain declarations for which the
   generated type of ``mkR`` is well-formed.

   .. code-block:: agda

      record R Γ : Setᵢ where
        constructor mkR
        field f₁ : A₁
        D₁
        field f₂ : A₂

      mkR : ∀ {Γ} (f₁ : A₁) (let D₁) (f₂ : A₂) → R Γ

.. _eta-expansion:

Eta-expansion
-------------

The eta rule for a record type

.. code-block:: agda

   record R : Set where
     field
       a : A
       b : B
       c : C

states that every ``x : R`` is definitionally equal to ``record { a =
R.a x ; b = R.b x ; c = R.c x }``. By default, all (inductive) record
types enjoy eta-equality if the positivity checker has confirmed it is
safe to have it. The keywords ``eta-equality``/``no-eta-equality``
enable/disable eta rules for the record type being declared.

.. _recursive-records:

Recursive records
-----------------

Recursive records need to be declared as either inductive or
coinductive.
::

  record Tree (A : Set) : Set where
    inductive
    constructor tree
    field
      elem     : A
      subtrees : List (Tree A)

  record Stream (A : Set) : Set where
    coinductive
    constructor _::_
    field
      head : A
      tail : Stream A

Inductive records have ``eta-equality`` on by default, while
``no-eta-equality`` is the default for coinductive records. In fact,
the ``eta-equality`` and ``inductive`` directives are not allowed
together, since this can easily make Agda loop. This can be overridden
at your own risk by using the pragma ``ETA`` instead.

It is possible to pattern match on inductive records, but not on
copinductive ones.

.. _instance-fields:

Instance fields
---------------

Instance fields, that is record fields marked with ``{{ }}`` can be used to
model "superclass" dependencies. For example::

  record Eq (A : Set) : Set where
    field
      _==_ : A → A → Bool

  open Eq {{...}}

.. code-block:: agda

  record Ord (A : Set) : Set where
    field
      _<_ : A → A → Bool
      {{eqA}} : Eq A

  open Ord {{...}} hiding (eqA)

Now anytime you have a function taking an ``Ord A`` argument the ``Eq A`` instance
is also available by virtue of η-expansion. So this works as you would expect:

.. code-block:: agda

  _≤_ : {A : Set} {{OrdA : Ord A}} → A → A → Bool
  x ≤ y = (x == y) || (x < y)

There is a problem however if you have multiple record arguments with conflicting
instance fields. For instance, suppose we also have a ``Num`` record with an ``Eq`` field

.. code-block:: agda

  record Num (A : Set) : Set where
    field
      fromNat : Nat → A
      {{eqA}} : Eq A

  open Num {{...}} hiding (eqA)

  _≤3 : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
  x ≤3 = (x == fromNat 3) || (x < fromNat 3)

Here the ``Eq A`` argument to ``_==_`` is not resolved since there are two conflicting
candidates: ``Ord.eqA OrdA`` and ``Num.eqA NumA``. To solve this problem you can declare
instance fields as *overlappable* using the ``overlap`` keyword::

  record Ord (A : Set) : Set where
    field
      _<_ : A → A → Bool
      overlap {{eqA}} : Eq A

  open Ord {{...}} hiding (eqA)

  record Num (A : Set) : Set where
    field
      fromNat : Nat → A
      overlap {{eqA}} : Eq A

  open Num {{...}} hiding (eqA)

  _≤3 : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
  x ≤3 = (x == fromNat 3) || (x < fromNat 3)

Whenever there are multiple valid candidates for an instance goal, if **all** candidates
are overlappable, the goal is solved by the left-most candidate. In the example above
that means that the ``Eq A`` goal is solved by the instance from the ``Ord`` argument.

Clauses for instance fields can be omitted when defining values of record
types. For instance we can define ``Nat`` instances for ``Eq``, ``Ord`` and
``Num`` as follows, leaving out cases for the ``eqA`` fields::

  instance
    EqNat : Eq Nat
    _==_ {{EqNat}} = Agda.Builtin.Nat._==_

    OrdNat : Ord Nat
    _<_ {{OrdNat}} = Agda.Builtin.Nat._<_

    NumNat : Num Nat
    fromNat {{NumNat}} n = n

