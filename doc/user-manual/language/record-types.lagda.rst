..
  ::
  {-# OPTIONS --guardedness --erasure #-}

  module language.record-types where

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat hiding (_==_; _<_)
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Reflection

  _||_ : Bool → Bool → Bool
  true  || x = true
  false || x = x

.. _record-types:

************
Record Types
************

.. contents::
   :depth: 2
   :local:

Records are types for grouping values together. They generalise the
dependent product type by providing named fields and (optional)
further components.

Example: the Pair type constructor
----------------------------------

Record types can be declared using the ``record`` keyword

..
  ::
  module Hide where

::

   record Pair (A B : Set) : Set where
     field
       fst : A
       snd : B

This defines a new type constructor ``Pair : Set → Set → Set`` and two
projection functions

.. code-block:: agda

  Pair.fst : {A B : Set} → Pair A B → A
  Pair.snd : {A B : Set} → Pair A B → B


.. note::

  The parameters ``A`` and ``B`` are implicit arguments to the projection
  functions.

  ::

   test-fst : {A B : Set} → Pair A B → A
   test-fst p = Pair.fst p

   test-snd : {A B : Set} → Pair A B → B
   test-snd p = Pair.snd p

You can ``open`` the record type to avoid the need to prefix projections
by the name of the record type (see :ref:`record modules <record-modules>`):

::

   open Pair

   test-fst' : {A B : Set} → Pair A B → A
   test-fst' p = fst p

   test-snd' : {A B : Set} → Pair A B → B
   test-snd' p = snd p

Elements of record types can be defined using a record expression, where
the associations are simple ``key = value`` pairs;

::

   p23 : Pair Nat Nat
   p23 = record { fst = 2; snd = 3 }

Using a ``record where`` expression, where the associations are treated
like :ref:`let bindings <let-expressions>`, in that they may refer to
previous bindings, may be parametrised, etc; Fields in a ``record
where`` expression can also be inherited from a module, by mentioning
all the bindings that should become fields in ``using`` or ``renaming``
clauses.

::

   p23' : Pair Nat Nat
   p23' = record where
      -- use the 'fst' binding in the module as the 'snd' field in this
      -- record:
      open Pair p23 using () renaming (fst to snd)
      fst = 2

or using :ref:`copatterns <copatterns>`. Copatterns may be used
prefix

::

   p34 : Pair Nat Nat
   Pair.fst p34 = 3
   Pair.snd p34 = 4

or postfix (in which case they are written prefixed with a dot)

::

   p56 : Pair Nat Nat
   p56 .Pair.fst = 5
   p56 .Pair.snd = 6

or using an :ref:`pattern lambda <pattern-lambda>`
(you may only use the postfix form of copatterns in this case)

::

   p78 : Pair Nat Nat
   p78 = λ where
     .Pair.fst → 7
     .Pair.snd → 8


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

Even if you did *not* use the ``constructor`` keyword, then it's still
possible to refer to the record's internally-constructor as a name,
using the syntax ``Record.constructor``; see
:ref:`anonymous-constructors` below for the details of this syntax.

::

  record Anon (A B : Set) : Set where
    field
      fst : A
      snd : B

  a45 : Anon Nat Nat
  a45 = Anon.constructor 4 5

In this sense, record types behave much like single constructor
datatypes (but see :ref:`eta-expansion` below).

.. _record-declarations:

Declaring, constructing and decomposing records
-----------------------------------------------

Declaring record types
~~~~~~~~~~~~~~~~~~~~~~~~

The general form of a record declaration is as follows:

.. code-block:: agda

   record <recordname> <parameters> : Set <level> where
     <directives>
     constructor <constructorname>
     field
       <fieldname1> : <type1>
       <fieldname2> : <type2>
       -- ...
     <declarations>

All the components are optional, and can be given in any order. In
particular, fields can be given in more than one block, interspersed
with other declarations. Each field is a component of the
record. Types of later fields can depend on earlier fields.

The directives available are ``eta-equality``, ``no-eta-equality``,
``pattern``
(see :ref:`eta-expansion`), ``inductive`` and ``coinductive`` (see
:ref:`recursive-records`).

Constructing record values
~~~~~~~~~~~~~~~~~~~~~~~~~~

Record values are constructed by giving a value for each record field:

.. code-block:: agda

   record { <fieldname1> = <term1> ; <fieldname2> = <term2> ; ... }

where the types of the terms match the types of the fields. If a
constructor ``<constructorname>`` has been declared for the record,
this can also be written

.. code-block:: agda

   <constructorname> <term1> <term2> ...

For named definitions, this can also be expressed using copatterns:

.. code-block:: agda

   <named-def> : <recordname> <parameters>
   <recordname>.<fieldname1> <named-def> = <term1>
   <recordname>.<fieldname2> <named-def> = <term2>
   ...

Records can also be constructed by :ref:`updating other records
<record-update>`.

.. _record-building-from-modules:

Building records from modules
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``record { <fields> }`` syntax also accepts module names. Fields
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

.. _anonymous-constructors:

Records with anonymous constructors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Even if a record was not defined with a named ``constructor`` directive,
Agda will still internally generate a constructor for the record. This
name is used internally to implement ``record{}`` syntax, but it can
still be obtained through using :ref:`reflection`. Since Agda 2.8.0,
it's possible to refer to this name from surface syntax as well:

::

  _ : Name
  _ = quote Anon.constructor

This syntax can be used wherever a name can be, and behaves exactly as
though the constructor had been named.

::

  {-# INLINE Anon.constructor #-}

However, keep in mind that the ``Record.constructor`` syntax is
*syntax*, and there is no binding for ``constructor`` in the module
``Anon``, nor is it possible to declare a function called
``constructor`` in another module. Moreover, the ``constructor``
pseudo-name is not affected by ``using``, ``hiding`` *or* ``renaming``
declarations, and attempting to list it in these is a syntax error.

The constructor of a record can be referred to whenever the record
itself is in scope, though note that if the record is abstract (see
:ref:`abstract-definitions`), it's still an error to refer to the
constructor:

.. code-block:: agda

  module _ where private
    record R : Set where

  abstract record S : Set where

  _ = R.constructor
  -- Name not in scope: R.constructor

  _ = S.constructor
  -- Constructor S.constructor is abstract, thus, not in scope here


.. _decomposing-records:

Decomposing record values
~~~~~~~~~~~~~~~~~~~~~~~~~

With the field name, we can project the corresponding component out of
a record value. Projections can be used either in prefix notation like
a function, or in postfix notation by adding a dot to the field name:

::

  sum-prefix : Pair Nat Nat → Nat
  sum-prefix p = Pair.fst p + Pair.snd p

  sum-postfix : Pair Nat Nat → Nat
  sum-postfix p = p .Pair.fst + p .Pair.snd

It is also possible to pattern match against inductive
records:

::

  sum-match : Pair Nat Nat → Nat
  sum-match (x , y) = x + y

Or, using a :ref:`let binding record pattern<let-record-pattern>`:

::

  sum-let : Pair Nat Nat → Nat
  sum-let p = let (x , y) = p in x + y


.. note::
   Naming the constructor is not required to enable pattern matching against
   record values. Record expressions can appear as patterns.


::

  sum-record-match : Pair Nat Nat → Nat
  sum-record-match record { fst = x ; snd = y } = x + y

.. _record-update:

Record update
~~~~~~~~~~~~~

Assume that we have a record type and a corresponding value:
::

  record MyRecord : Set where
    field
      a b c : Nat

  old : MyRecord
  old = record { a = 1; b = 2; c = 3 }

Then we can update (some of) the record value’s fields in the following way:
::

  new : MyRecord
  new = record old { a = 0; c = 5 }

or using the ``record where`` syntax
::

  new₁ : MyRecord
  new₁ = record old where
    a = 0
    c = 5

Here ``new`` normalises to ``record { a = 0; b = 2; c = 5 }``. Any
expression yielding a value of type ``MyRecord`` can be used instead of
``old``. Using that :ref:`records can be built from module names
<record-building-from-modules>`, together with the fact that
:ref:`all records define a module <record-modules>`, this can also be
written as

::

  new₂ : MyRecord
  new₂  = record { MyRecord old; a = 0; c = 5}

..
  ::
  -- make sure the syntax doesn't matter
  _ : new ≡ new₁
  _ = refl
  _ : new ≡ new₂
  _ = refl

Record updating is not allowed to change types: the resulting value
must have the same type as the original one, including the record
parameters. Thus, the type of a record update can be inferred if the
type of the original record can be inferred.

The record update syntax is expanded before type checking. When the
expression

.. code-block:: agda

  record old { upd-fields }

is checked against a record type ``R``, it is expanded to

.. code-block:: agda

  let r = old in record { new-fields }

where ``old`` is required to have type ``R`` and ``new-fields`` is defined as
follows: for each field ``x`` in ``R``,

  - if ``x = e`` is contained in ``upd-fields`` then ``x = e`` is
    included in ``new-fields``, and otherwise
  - if ``x`` is an explicit field then ``x = R.x r`` is included in
    ``new-fields``, and
  - if ``x`` is an :ref:`implicit <implicit-arguments>` or :ref:`superclass <instance-fields>` field, then it is omitted from ``new-fields``.

The reason for treating implicit and superclass fields specially is to
allow code like the following::

  data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

  record VList : Set where
    field
      {length} : Nat
      vec      : Vec Nat length
      -- More fields ...

  xs : VList
  xs = record { vec = 0 ∷ 1 ∷ 2 ∷ [] }

  ys = record xs { vec = 0 ∷ [] }

Without the special treatment the last expression would need to
include a new binding for ``length`` (for instance ``length = _``).


.. _record-modules:

Record modules
--------------

Along with a new type, a record declaration also defines a module with the same name, parameterised
over an element of the record type containing
the projection functions. This allows records to be "opened", bringing the
fields into scope. For instance

::

  swap : {A B : Set} → Pair A B → Pair B A
  swap p = snd , fst
    where open Pair p

In the example, the record module ``Pair`` has the shape

.. code-block:: agda

  module Pair {A B : Set} (p : Pair A B) where
    fst : A
    snd : B

.. note::
  This is not quite right: The projection functions take the
  parameters as :ref:`erased <runtime-irrelevance>` arguments.
  However, the parameters are not erased in the module telescope if
  they were not erased to start with.

It's possible to add arbitrary definitions to the record module, by defining them
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

The eta (η) rule for a record type

..
  ::
  import Agda.Builtin.Equality
  postulate A B C : Set

::

  record R : Set where
     field
       a : A
       b : B
       c : C

states that every ``x : R`` is definitionally equal to ``record { a =
R.a x ; b = R.b x ; c = R.c x }``.

::

  eta-R : (x : R) → x ≡ record { a = R.a x ; b = R.b x ; c = R.c x }
  eta-R r = refl

By default, all non-recursive record types enjoy η-equality. The keywords
``eta-equality``/``no-eta-equality`` enable/disable η rules for the record type
being declared.

::

  record R-noeta : Set where
    no-eta-equality
    field
      a : A
      b : B
      c : C

.. _recursive-records:

Recursive records
-----------------

A recursive record is a record where the record type itself appears in the type
of one of its fields. Recursive records need to be declared as either
``inductive`` or ``coinductive``.

Inductive records
~~~~~~~~~~~~~~~~~

Inductive records are recursive records that only allow values of finite depth.

::

  record Tree (A : Set) : Set where
    inductive
    constructor tree
    field
      elem     : A
      subtrees : List (Tree A)

  open Tree

Inductive record types (see :ref:`recursive-records`) have η-equality enabled by
default if this does not lead to potential infinite η-expansion (as determined
by the :ref:`positivity checker<positivity-checking>`).

::

  eta-Tree : {A : Set} (t : Tree A) → t ≡ tree (elem t) (subtrees t)
  eta-Tree t = refl

It is possible to pattern match and recurse on an inductive record if it has η-equality:

::

  map-Tree : {A B : Set} → (A → B) → Tree A → Tree B
  map-Tree {A} {B} f (tree x ts) = tree (f x) (map-subtrees ts)
    where
      map-subtrees : List (Tree A) → List (Tree B)
      map-subtrees [] = []
      map-subtrees (t ∷ ts) = map-Tree f t ∷ map-subtrees ts

For inductive record types *without* η-equality, pattern matching is not allowed
by default. Pattern matching can be turned on manually by using the ``pattern``
record directive:

::

  record HereditaryList : Set where
    inductive
    no-eta-equality
    pattern
    field sublists : List HereditaryList

  pred : HereditaryList → List HereditaryList
  pred record{ sublists = ts } = ts

If both ``eta-equality`` and ``pattern`` are given for a record types,
Agda will alert the user of a redundant ``pattern`` directive.
However, if η is inferred but not declared explicitly, Agda will just
ignore a redundant ``pattern`` directive; this is because the default
can be changed globally by option :option:`--no-eta-equality`.

.. note::

  It is not allowed to use copattern matching to define values of inductive
  record types with pattern matching enabled. This combination leads to either a
  loss of canonicity or a loss of subject reduction. For example, consider the
  following definitions:

  .. code-block:: agda

    record Rec : Set where
      constructor con
      no-eta-equality
      field
        f : Nat
    open Rec

    eta : (r : Rec) → r ≡ con (f r)
    eta (con n) = refl

    bar : R
    f bar = 0

  If this code were allowed, then ``eta bar`` is a closed term of type
  ``bar ≡ con 0``. Now either ``eta bar`` reduces to
  ``refl : bar ≡ con 0`` (contradicting the ``no-eta-equality`` directive)
  or else ``eta bar`` is a stuck term (breaking canonicity).

Coinductive records
~~~~~~~~~~~~~~~~~~~

Coinductive records are recursive records that allow values of possibly infinite
depth.

::

  record Stream (A : Set) : Set where
    coinductive
    constructor _::_
    field
      head : A
      tail : Stream A

  open Stream

Values of coinductive records can be defined using copatterns:

::

  natsFrom : Nat → Stream Nat
  head (natsFrom n) = n
  tail (natsFrom n) = natsFrom (suc n)

Constructors of records supporting copattern matching may be marked with an
``{-# INLINE #-}`` :ref:`pragma <inline-pragma>`. This will automatically
convert uses of the constructor to the equivalent definition using copatterns,
which can be useful to assist the termination checker.

Eta equality for coinductive records is not allowed, since this combination
could easily make Agda loop. This can be overridden at your own risk by using
the :ref:`ETA <eta-pragma>` instead. Pattern matching on coinductive records is
likewise not allowed.

You can read more about coinductive records in the section on
:ref:`coinduction <copatterns-coinductive-records>`.

.. _instance-fields:

Records and instance search
---------------------------

The fields of a record type can interact with the :ref:`instance search
<instance-arguments>` mechanism in two orthogonal ways.

1. A record field can be given instance *visibility*, by wrapping its
   name in double braces ``{{ }}``. To disambiguate, we refer to record
   fields with instance visibility as **superclass fields**.

   Superclass fields are instance arguments to the record constructor.
   This means that they :ref:`can often be omitted
   <superclass-omission>`.

2. The field declaration itself can be nested in an ``instance`` block.
   We refer to these as (having) **instance projections**.

   Making a record field into an instance projection does *not* alter
   the visibility with which it is bound, meaning that, unless it is
   additionally made into a superclass field (or into a hidden argument
   to the record constructor), it must be explicitly specified when
   constructing a record value.

..
  ::

  module Both where
    postulate Ex1 : Set → Set

Any given record field can be made into both an instance projection
*and* a superclass field. It will then be subject to *both* of the
behaviours described in the following sections::

    record Ex2 (A : Set) : Set where
      field
        instance ⦃ both ⦄ : Ex1 A

Both superclass fields and instance projections can appear any number of
times in a record declaration, and in any position in the list of
fields.

.. _superclass-fields:

Superclass fields
~~~~~~~~~~~~~~~~~

..
  ::

  module Instances-no-overlap where

As the name implies, superclass fields are used to model superclass
relationships (in the Haskell sense). For example, we can define a class
``Ord`` that "extends" a class ``Eq`` by defining a pair of record
types, where an ``Ord`` value has a superclass field of ``Eq`` type::

    record Eq (A : Set) : Set where
      field
        _==_ : A → A → Bool

    open Eq ⦃ ... ⦄

    record Ord (A : Set) : Set where
      field
        _<_     : A → A → Bool
        ⦃ eqA ⦄ : Eq A

    open Ord ⦃ ... ⦄ hiding (eqA)

As long as ``Ord`` is an :ref:`eta record <eta-expansion>`, local
*instance* variables of type ``Ord A`` will also bring ``Eq A``
instances into scope. For example, a function taking an ``Ord A``
instance argument can also use an ``Eq`` instance::

    _≤_ : {A : Set} ⦃ ordA : Ord A ⦄ → A → A → Bool
    x ≤ y = (x == y) || (x < y)

Superclass fields are **only** brought into scope if the "subclass"
variable is in scope *as an instance*. The following will not work:

.. code-block:: agda

    weird : {A : Set} (ordA : Ord A) → A → A → Bool
    weird _ = x == y

However, since superclass fields are instance arguments to a
constructor, they can be manually brought into scope by matching on the
record value. Keep in mind that if the record value had non-instance
visibility, then the **subclass** will not be available for instance
search, even after pattern matching::

    works : {A : Set} (ordA : Ord A) → A → A → Bool
    works record{} x y = x == y
    -- Matching on record{} makes all the fields into local variables,
    -- including the superclass fields.

.. code-block:: agda

    fails : {A : Set} (ordA : Ord A) → A → A → Bool
    fails record{} x y = x ≤ y
    -- No instance of type Ord A was found in scope.
    -- Since the Ord argument is visible, it is totally ignored by
    -- instance search.

.. warning::

  Superclass fields are brought into the local instance table by
  **expanding local instance variables**. This means that Agda can fail
  to find an instance of a subclass *even if* the corresponding
  superclass is derivable. For example, we can explicitly provide the
  ``eqA`` field of an ``Ord`` instance when constructing it, even if
  there is no corresponding instance in scope::

    instance
      OrdNat : Ord Nat
      OrdNat = record
        { _<_ = Agda.Builtin.Nat._<_
        ; eqA = record { _==_ = Agda.Builtin.Nat._==_ }
        -- no global Eq Nat instance!
        }

  Attempting to search for an ``Eq Nat`` instance will then fail,
  because superclass field expansion *only* applies to local variables
  with instance visibility, and not to top-level instance declarations.

  .. code-block:: agda

      fails : Bool
      fails = 1 == 2
      -- No instance of type Eq Nat was found in scope.

Eta-expanding instance variables to find superclass fields will also
work under binders, which means that a *family* of subclass instances
gets expanded into a *family* of instances for the corresponding
superclass::

    fam
      : {Ix : Set} {F : Ix → Set} ⦃ ords : ∀ {i} → Ord (F i) ⦄
      → (ix : Ix) → F ix → F ix → Bool
    fam ix x y = x == y

If the type of a superclass field is *itself* a record type with
superclass fields, then it will be expanded recursively::

    data ORD : Set where
      lt le eq : ORD

    record Cmp (A : Set) : Set where
      field
        ⦃ ordA ⦄ : Ord A
        compare  : A → A → ORD

    cmp→eq : {A : Set} ⦃ ordA : Cmp A ⦄ → A → A → Bool
    cmp→eq x y = x == y

Superclass fields are in scope as local instances in the types of
subsequent fields, and in the types of any declarations nested within
the record::

    record Interval (A : Set) : Set where
      field
        ⦃ cmpA ⦄ : Cmp A
        lo hi    : A

      -- Declaration *between* fields:
      ordered : Bool
      ordered = lo < hi

      field in-order : ordered ≡ true

      -- Declaration *after* fields:
      is-empty : Bool
      is-empty = lo == hi

Any subsequent declaration within the record can depend on its
superclass fields through instance search, and these fields are
themselves available for superclass expansion.

.. warning::

  Opening a record module, even locally, will **not** make superclass
  fields into local instances. Only the :ref:`instance projections
  <instance-projections>` will be brought into scope by a module
  application.

  .. code-block:: agda

      fails : {A : Set} (ordA : Ord A) → A → A → Bool
      fails ord x y = let open Ord ord in x == y
      -- no instance of Eq A in scope, since the superclass field eqA does
      -- not have an instance projection

Overlapping superclass fields
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
..
  ::

  module Instances-overlap where
    record Eq (A : Set) : Set where
      field
        _==_ : A → A → Bool

    open Eq ⦃ ... ⦄

When multiple subclasses "inherit" from the same class, superclass field
expansion will produce distinct candidates for the superclass by
expanding each of the subclasses. In this situation, instance search
will fail with an unresolved overlap.

This can be remedied by marking **all** of the relevant superclass
fields with the ``overlap`` keyword. For example, we can define a
``Num`` class that also "extends" ``Eq``, as long as ``Ord`` is
redefined to have its ``Eq`` superclass field also marked ``overlap``::

    record Ord (A : Set) : Set where
      field
        _<_     : A → A → Bool
        overlap ⦃ eqA ⦄ : Eq A

    record Num (A : Set) : Set where
      field
        fromNat         : Nat → A
        overlap ⦃ eqA ⦄ : Eq A

    open Ord ⦃ ... ⦄ hiding (eqA)
    open Num ⦃ ... ⦄ hiding (eqA)

We can now define a function that takes both ``Num`` and ``Ord``
instances::

    _≤3 : {A : Set} ⦃ ordA : Ord A ⦄ ⦃ numA : Num A ⦄ → A → Bool
    x ≤3 = (x == fromNat 3) || (x < fromNat 3)

When all possible candidates for an instance constraint arise from
superclass fields marked ``overlap``, instance search will choose the
field arising from the leftmost record value. In the function above,
that is the candidate coming from the ``Ord`` argument::

    _
      : {A : Set} ⦃ ordA : Ord A ⦄ ⦃ numA : Num A ⦄ {arg : A}
      → (arg ≤3) ≡ ((_==_ ⦃ Ord.eqA ordA ⦄ arg (fromNat 3)) || _)
    _ = refl

If overlapping candidates are introduced by *recursive* superclass
expansion, resolution will prefer those arising from the earlier field
in declaration order. Candidates expanded 'on the way' do not,
themselves, need to be marked overlap; Nor will this be sufficient for
resolving an overlap in *their* superclass fields.

::

    record NumOrd (A : Set) : Set where
      field
        ⦃ numA ⦄ : Num A
        ⦃ ordA ⦄ : Ord A

    _≤4 : {A : Set} ⦃ numordA : NumOrd A ⦄ → A → Bool
    x ≤4 = (x == fromNat 4) || (x < fromNat 4)

..
  ::
    open NumOrd
    open Num hiding (fromNat)

Here, the ``Eq`` instance is selected from the ``numA`` field of the
``NumOrd`` argument::

    _
      : {A : Set} ⦃ numordA : NumOrd A ⦄ {arg : A}
      → (arg ≤4) ≡ ((_==_ ⦃ numordA .numA .eqA ⦄ arg (fromNat 4)) || _)
    _ = refl

.. _superclass-omission:

Omitting superclass fields
^^^^^^^^^^^^^^^^^^^^^^^^^^

Since superclass fields become instance arguments to the constructor,
they can be omitted when the constructor is applied as a function, when
using either form of ``record`` expression, and when defining a value of
the record by copattern matching. In any of these cases, the missing
fields will be filled by instance search::

    instance
      EqNat : Eq Nat
      EqNat ._==_ = Agda.Builtin.Nat._==_

    ex1 ex2 ex3 : Ord Nat
    ex1 ._<_ = Agda.Builtin.Nat._<_
    ex2 = record { _<_ = Agda.Builtin.Nat._<_ }
    ex3 = record where
      _<_ = Agda.Builtin.Nat._<_

.. _instance-projections:

Instance projections
~~~~~~~~~~~~~~~~~~~~

..
  ::

  module Instproj where
    record Eq (A : Set) : Set where
      field
        _==_ : A → A → Bool

    open Eq ⦃ ... ⦄

A record field defined in a nested ``instance`` block makes the
projection function into a top-level instance declaration nested in the
record module. It does not affect the visibility of the field in the
record constructor's telescope::

    record Eqtype : Set₁ where
      no-eta-equality -- (!)
      field
        carrier      : Set
        instance eqA : Eq carrier

    open Eqtype renaming (carrier to [_])

A priori, this has no effect on the instance table, since definitions
within the record module take the record as a **visible** argument.
However, if the record module is instantiated, as long as the type of
the resulting instantiation is a valid type for an instance, the
projection will become usable as an instance, at the instantiated
type::

    example : (T : Eqtype) → [ T ] → [ T ] → Bool
    example T x y = let open Eqtype T in x == y

In the example above, the local declarations introduced by the ``let
open Eqtype T`` expression are equivalent to::

    example' : (T : Eqtype) → [ T ] → [ T ] → Bool
    example' T x y =
      let
        carrier = Eqtype.carrier T
        instance
          eqA : Eq carrier
          eqA = Eqtype.eqA T
      in x == y

.. note::

  Because instance projections are brought into scope by instantiations
  of the record module, they work even if they belong to a
  ``no-eta-equality`` record type.

Since instance projections are fully equivalent to defining a top-level
``instance`` in the record module, they can be annotated with one of the
:ref:`overlap pragmas <overlapping-instances>` for fine-grained control
of the overlapping behaviour of the instances resulting from an
application of the record module.

.. warning::

  If an instance projection has a :ref:`modality <modalities>` that
  prevents it from having a corresponding top-level projection (e.g., it
  is irrelevant, and :option:`--irrelevant-projections` was not given),
  instantiating the record module will **not** bring it into scope as an
  instance::

    postulate
      Nonzero : Nat → Set
      _/_ : Nat → (div : Nat) ⦃ _ : Nonzero div ⦄ → Nat

    record Pos : Set where
      field
        num : Nat
        instance .pos : Nonzero num

  Attempting to use the ``pos`` field as an instance by opening the
  module ``Pos`` will fail.

  .. code-block:: agda

    fails : (x : Nat) (y : Pos) → Nat
    fails x y = let open Pos y in x / num
    -- The field 'pos' has no projection, so:
    -- No instance of type Nonzero num was found in scope.
