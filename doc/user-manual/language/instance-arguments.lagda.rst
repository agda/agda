..
  ::
  {-# OPTIONS --rewriting --sized-types #-}
  module language.instance-arguments where

  open import language.built-ins
    using (Bool; true; false; List; _∷_; []; Nat; _-_; zero; suc; _+_; String; Int)
    renaming (_==_ to _≡ᵇ_)

  open import Agda.Primitive

  postulate undefined : ∀ {u} {A : Set u} → A

.. _instance-arguments:

******************
Instance Arguments
******************

.. contents::
   :depth: 1
   :local:

Instance arguments are a special kind of :ref:`implicit arguments
<implicit-arguments>` that get solved by a special :ref:`instance
resolution <instance-resolution>` algorithm, rather than by the
unification algorithm used for normal implicit arguments.
Instance arguments are the Agda equivalent of Haskell type class
constraints and can be used for many of the same purposes.

An instance argument will be resolved if its type is a *named type*
(i.e. a data type or record type) or a *variable type* (i.e. a
previously bound variable of type `Set ℓ`), and a unique *instance* of
the required type can be built from :ref:`declared
instances <declaring-instances>` and the current context.

Usage
-----

Instance arguments are enclosed in double curly braces ``{{ }}``, e.g. ``{{x : T}}``.
Alternatively they can be enclosed, with proper spacing, e.g. ``⦃ x : T ⦄``, in the
unicode braces ``⦃ ⦄`` (``U+2983`` and ``U+2984``, which can be typed as
``\{{`` and ``\}}`` in the :ref:`Emacs mode <unicode-input>`).

For instance, given a function ``_==_``

..
  ::

  _||_ : Bool → Bool → Bool
  true  || _ = true
  false || y = y

  _&&_ : Bool → Bool → Bool
  false && _ = false
  true  && y = y

  infixl 10 _||_ _&&_

  _++_ : ∀ {u} {A : Set u} → List A → List A → List A
  [] ++ xs = xs
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  module eq-prototype (Eq : Set → Set) where

::

    _==_ : {A : Set} {{eqA : Eq A}} → A → A → Bool

..
  ::
    _==_ = undefined

for some suitable type ``Eq``, you might define

..
  ::
    module elem-one where

::

      elem : {A : Set} {{eqA : Eq A}} → A → List A → Bool
      elem x (y ∷ xs) = x == y || elem x xs
      elem x []       = false

Here the instance argument to ``_==_`` is solved by the corresponding argument
to ``elem``. Just like ordinary implicit arguments, instance arguments can be
given explicitly. The above definition is equivalent to

..
  ::
    module elem-bis where

::

      elem : {A : Set} {{eqA : Eq A}} → A → List A → Bool
      elem {{eqA}} x (y ∷ xs) = _==_ {{eqA}} x y || elem {{eqA}} x xs
      elem         x []       = false

A very useful function that exploits this is the function ``it`` which lets you
apply instance resolution to solve an arbitrary goal::

  it : ∀ {a} {A : Set a} → {{A}} → A
  it {{x}} = x

As the last example shows, the name of the instance argument can be
omitted in the type signature:

..
  ::
  module example-underscore (Eq : Set → Set) where

::

     _==_ : {A : Set} → {{Eq A}} → A → A → Bool

..
  ::
     _==_ = undefined

Defining type classes
~~~~~~~~~~~~~~~~~~~~~

The type of an instance argument should have the form ``{Γ} → C vs``,
where ``C`` is a postulated name, a bound variable, or the name of a
data or record type, and ``{Γ}`` denotes an arbitrary number of
implicit or instance arguments (see :ref:`dependent-instances` below
for an example where ``{Γ}`` is non-empty).

Instances with explicit arguments are also accepted but will not be
considered as instances because the value of the explicit arguments
cannot be derived automatically. Having such an instance has no effect
and thus raises a warning.

Instance arguments whose types end in any other type are currently
also accepted but cannot be resolved by instance search, so they must
be given by hand. For this reason it is not recommended to use such
instance arguments. Doing so will also raise a warning.

Other than that there are no requirements on the type of an instance
argument. In particular, there is no special declaration to say that a
type is a "type class". Instead, Haskell-style type classes are
usually defined as :ref:`record types <record-types>`. For instance,

::

  record Monoid {a} (A : Set a) : Set a where
    field
      mempty : A
      _<>_   : A → A → A

In order to make the fields of the record available as functions taking
instance arguments you can use the special module application

..
  ::
  module monoid-record-open where

::

    open Monoid {{...}} public

This will bring into scope

..
  ::
  module open-prototypes where

::

    mempty : ∀ {a} {A : Set a} → {{Monoid A}} → A
    _<>_   : ∀ {a} {A : Set a} → {{Monoid A}} → A → A → A

..
  ::
    mempty = undefined
    _<>_   = undefined

Superclass dependencies can be implemented using :ref:`instance-fields`.

See :ref:`module-application` and :ref:`record-modules` for details about how
the module application is desugared. If defined by hand, ``mempty`` would be

..
  ::
  module mempty-by-hand where

::


    mempty : ∀ {a} {A : Set a} → {{Monoid A}} → A
    mempty {{mon}} = Monoid.mempty mon

Although record types are a natural fit for Haskell-style type
classes, you can use instance arguments with data types to good
effect. See the :ref:`instance-arguments-examples` below.

.. _declaring-instances:

Declaring instances
~~~~~~~~~~~~~~~~~~~

As seen above, instance arguments in the context are available when solving
instance arguments, but you also need to be able to
define top-level instances for concrete types. This is done using the
``instance`` keyword, which starts a :ref:`block <lexical-structure-layout>` in
which each definition is marked as an instance available for instance
resolution. For example, an instance ``Monoid (List A)`` can be defined as

..
  ::
  module list-monoid where

::

    instance
      ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)
      ListMonoid = record { mempty = []; _<>_ = _++_ }

Or equivalently, using :ref:`copatterns <copatterns>`:

..
  ::
  open Monoid {{...}} public

::

  instance
    ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)
    mempty {{ListMonoid}} = []
    _<>_   {{ListMonoid}} xs ys = xs ++ ys

Top-level instances must target a named type (``Monoid`` in this case), and
cannot be declared for types in the context.

You can define local instances in let-expressions in the same way as a
top-level instance. For example::

  mconcat : ∀ {a} {A : Set a} → {{Monoid A}} → List A → A
  mconcat [] = mempty
  mconcat (x ∷ xs) = x <> mconcat xs

  sum : List Nat → Nat
  sum xs =
    let instance
          NatMonoid : Monoid Nat
          NatMonoid = record { mempty = 0; _<>_ = _+_ }
    in mconcat xs

Instances can have instance arguments themselves, which will be filled in
recursively during instance resolution. For instance,

..
  ::
  module eq-list where

::

    record Eq {a} (A : Set a) : Set a where
      field
        _==_ : A → A → Bool

    open Eq {{...}} public

    instance
      eqList : ∀ {a} {A : Set a} → {{Eq A}} → Eq (List A)
      _==_ {{eqList}} []       []       = true
      _==_ {{eqList}} (x ∷ xs) (y ∷ ys) = x == y && xs == ys
      _==_ {{eqList}} _        _        = false

      eqNat : Eq Nat
      _==_ {{eqNat}} = _≡ᵇ_  -- imported from Data.Nat.Base

    ex : Bool
    ex = (1 ∷ 2 ∷ 3 ∷ []) == (1 ∷ 2 ∷ []) -- false

Note the two calls to ``_==_`` in the right-hand side of the second clause. The
first uses the ``Eq A`` instance and the second uses a recursive call to
``eqList``. In the example ``ex``, instance resolution, needing a value of type ``Eq
(List Nat)``, will try to use the ``eqList`` instance and find that it needs an
instance argument of type ``Eq Nat``, it will then solve that with ``eqNat``
and return the solution ``eqList {{eqNat}}``.

.. note::
   At the moment there is no termination check on instances, so it is possible
   to construct non-sensical instances like
   ``loop : ∀ {a} {A : Set a} → {{Eq A}} → Eq A``.
   To prevent looping in cases like this, the search depth of instance search
   is limited, and once the maximum depth is reached, a type error will be
   thrown. You can set the maximum depth using the :option:`--instance-search-depth`
   flag.

Restricting instance search
~~~~~~~~~~~~~~~~~~~~~~~~~~~

To restrict an instance to the current module, you can mark it as
`private`. For instance,

..
  ::
  module private-instance where

    open import Agda.Builtin.Equality

::

    record Default (A : Set) : Set where
      field default : A

    open Default {{...}} public

    module M where

      private
        instance
          defaultNat : Default Nat
          defaultNat .default = 6

      test₁ : Nat
      test₁ = default

      _ : test₁ ≡ 6
      _ = refl

    open M

    instance
      defaultNat : Default Nat
      defaultNat .default = 42

    test₂ : Nat
    test₂ = default

    _ : test₂ ≡ 42
    _ = refl

Alternatively, you can enable the :option:`--no-qualified-instances` flag to
make Agda only consider instances from modules that have been opened
(see :ref:`below<qualified-instances>` for more details).

..

Constructor instances
+++++++++++++++++++++

Although instance arguments are most commonly used for record types,
mimicking Haskell-style type classes, they can also be used with data
types. In this case you often want the constructors to be instances,
which is achieved by declaring them inside an ``instance``
block. Constructors can only be declared as instances if all their
arguments are implicit or instance arguments. See
:ref:`instance-resolution` below for the details.

A simple example of a constructor that can be made an instance is the
reflexivity constructor of the equality type::

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    instance refl : x ≡ x

..
  ::
  infix 4 _≡_

This allows trivial equality proofs to be inferred by instance resolution,
which can make working with functions that have preconditions less of a burden.
As an example, here is how one could use this to define a function that takes a
natural number and gives back a ``Fin n`` (the type of naturals smaller than
``n``)::

  data Fin : Nat → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)

  mkFin : ∀ {n} (m : Nat) → {{suc m - n ≡ 0}} → Fin n
  mkFin {zero}  m {{}}
  mkFin {suc n} zero    = zero
  mkFin {suc n} (suc m) = suc (mkFin m)

  five : Fin 6
  five = mkFin 5 -- OK

.. code-block: agda
  badfive : Fin 5
  badfive = mkFin 5 -- Error: No instance of type 1 ≡ 0 was found in scope.

In the first clause of ``mkFin`` we use an :ref:`absurd pattern
<absurd-patterns>` to discharge the impossible assumption ``suc m ≡
0``.  See the :ref:`next section <instance-arguments-examples>` for
another example of constructor instances.

Record fields can also be declared instances, with the effect that the
corresponding projection function is considered a top-level instance.

.. _qualified-instances:

Qualified instances
+++++++++++++++++++

By default, Agda considers all instances as candidates, even if they
are only in scope under a qualified name. In particular, this means
that instances from a module that is ``import``-ed but not ``open``-ed
are still considered for instance search. You can use the
:option:`--no-qualified-instances` flag to make Agda instead only consider
instances that are in scope under an unqualified name.

As an example, consider the following Agda code:

::

  record MyClass (A : Set) : Set where
    field
      myFun : A → A
  open MyClass {{...}}

  module Instances where

    instance myNatInstance : MyClass Nat
    myFun {{myNatInstance}} = suc

  -- without --no-qualified-instances
  test1 : Nat
  test1 = myFun 41

By default, this example is accepted by Agda, but if
:option:`--no-qualified-instances` is enabled you have to open the module
``Instances`` first:

::

  -- with --no-qualified-instances
  open Instances

  test2 : Nat
  test2 = myFun 41

This flag can be especially useful if you want to import a module
without necessarily using all of the instances that it exports.

.. _instance-arguments-examples:

Examples
~~~~~~~~

.. _dependent-instances:

Dependent instances
+++++++++++++++++++

..
  ::
  data Maybe {a} (A : Set a) : Set a where
    nothing : Maybe A
    just    : A → Maybe A

  module dependent-instances where
    open Agda.Primitive

Consider a variant on the ``Eq`` class where the equality function produces a
proof in the case the arguments are equal::

    record Eq {a} (A : Set a) : Set a where
      field
        _==_ : (x y : A) → Maybe (x ≡ y)

    open Eq {{...}} public

A simple boolean-valued equality function is problematic for types with
dependencies, like the Σ-type

::

    data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
      _,_ : (x : A) → B x → Σ A B

since given two pairs ``x , y`` and ``x₁ , y₁``, the types of the second
components ``y`` and ``y₁`` can be completely different and not admit an
equality test. Only when ``x`` and ``x₁`` are *really equal* can we hope to
compare ``y`` and ``y₁``. Having the equality function return a proof means
that we are guaranteed that when ``x`` and ``x₁`` compare equal, they really
are equal, and comparing ``y`` and ``y₁`` makes sense.

An ``Eq`` instance for ``Σ`` can be defined as follows::

    instance
      eqΣ : ∀ {a b} {A : Set a} {B : A → Set b} → {{Eq A}} → {{∀ {x} → Eq (B x)}} → Eq (Σ A B)
      _==_ {{eqΣ}} (x , y) (x₁ , y₁) with x == x₁
      _==_ {{eqΣ}} (x , y) (x₁ , y₁)    | nothing = nothing
      _==_ {{eqΣ}} (x , y) (.x , y₁)    | just refl with y == y₁
      _==_ {{eqΣ}} (x , y) (.x , y₁)    | just refl    | nothing   = nothing
      _==_ {{eqΣ}} (x , y) (.x , .y)    | just refl    | just refl = just refl

Note that the instance argument for ``B`` states that there should be
an ``Eq`` instance for ``B x``, for any ``x : A``. The argument ``x``
must be implicit, indicating that it needs to be inferred by
unification whenever the ``B`` instance is used. See
:ref:`instance-resolution` below for more details.


.. _overlap-backtracking:

Overlap and backtracking
------------------------

By default, instance resolution does not make unforced choices between
instances. In practice, this means that instances may not *overlap*: if
there are multiple candidates that could be used to solve an instance
goal, a type error is raised.

For example, imagine that we have two separate printing classes: one for
printing a debug representation, which we will call ``Show``, and one
for pretty printing, called ``Pretty``. Since quite a few types (e.g.
integers) have identical debug and pretty representations, we could try
having a "default" instance for ``Pretty``, in terms of ``Show``::

  record Show (A : Set) : Set where
    field show : A → String
  open Show ⦃ ... ⦄

  record Pretty (A : Set) : Set where
    field pretty : A → String
  open Pretty ⦃ ... ⦄

  instance
    pretty-show : ∀ {a} ⦃ _ : Show a ⦄ → Pretty a
    pretty-show = record { pretty = show }

Of course, some values have distinct representations. For example, we
might want to pretty-print lists in square brackets, instead of as
cons-cells. We write an instance::

  postulate instance
    show-nat : Show Nat
    pretty-list : ∀ {a} ⦃ _ : Pretty a ⦄ → Pretty (List a)

However, if we try printing a list of numbers, Agda complains about
overlap! While the ``pretty-list`` instance is strictly more specific
than ``pretty-show``, neither candidate is inapplicable in this
situation, so Agda refuses to choose.

.. code-block:: text

  Failed to solve the following constraints:
    Resolve instance argument _r_273 : Pretty (List Nat)
    Candidates
      pretty-show : {a : Set} ⦃ _ : Show a ⦄ → Pretty a
      pretty-list : {a : Set} ⦃ _ : Pretty a ⦄ → Pretty (List a)

.. _overlapping-instances:

Overlapping instances
~~~~~~~~~~~~~~~~~~~~~

To support situations like ``Pretty`` above, Agda allows the user to
specify, on a per-instance basis, what should happen when multiple
candidates are available. This is done using one of the following four
pragmas:

* An ``OVERLAPPABLE`` instance can be discarded in favour of a strictly
  *more* specific instance.

* An ``OVERLAPPING`` instance can cause strictly *less* specific
  instances to be discarded.

* The convenience pragma ``OVERLAPS`` is equivalent to ``OVERLAPPABLE``
  and ``OVERLAPPING``. This means that it can both cause less specific
  instances to be discarded, *and* it can be discarded if a more
  specific candidate is available.

* An ``INCOHERENT`` instance can be arbitrarily discarded in favour of
  another possible candidate.

An instance ``c1 : ∀ {Γ} → C xs`` is **more specific** than an instance
``T2 : ∀ {Δ} → C ys`` if there is an instantiation of the variables
``Δ`` which makes ``ys`` definitionally equal to ``xs``. We say that
``c1`` is **strictly** more specific than ``c2`` if ``c1`` is more
specific than ``c2`` and ``c2`` is *not* more specific than ``c1``.

Returning to the ``Pretty`` example, we can make the more specific
instance(s) be selected by marking the ``pretty-show`` instance
``OVERLAPPABLE``::

  {-# OVERLAPPABLE pretty-show #-}
  _ : String
  _ = pretty (1 ∷ 2 ∷ 3 ∷ [])

It would also have been possible to mark the ``pretty-list`` instance
``OVERLAPPING``.

Overlap resolution considers *strict* specificity to keep Agda from
making unforced choices. If multiple candidates have "the same
specificity", then no matter whether they are both overlappable, the
instance constraint still goes unsolved. An example is the following
situation::

  postulate
    C   : Set → Set → Set
    instance
      CIa : ∀ {a} → C Int a
      CaI : ∀ {a} → C a Int
    {-# OVERLAPS CIa CaI #-}

When solving the goal ``C Int Int``, neither candidate can be discarded
in favour of the other. You can make the choice yourself by marking the
candidate that should **not** be used as ``INCOHERENT`` instead of
``OVERLAPS``.

.. _backtracking-instances:

Backtracking
~~~~~~~~~~~~

By default, Agda only considers an instance's final return type when
considering whether an instance is applicable. In particular, the
instance search algorithm does not backtrack, and whether or not an
instance's constraints are satisfied does not factor into overlap
resolution.

For example, in code below, the instances ``zero`` and ``suc`` overlap
for the goal ``ex₁``, because either one of them can be used to solve
the goal when given appropriate arguments, so instance search will fail.

.. code-block:: agda

  infix 4 _∈_
  data _∈_ {A : Set} (x : A) : List A → Set where
    instance
      zero : ∀ {xs} → x ∈ x ∷ xs
      suc  : ∀ {y xs} → {{x ∈ xs}} → x ∈ y ∷ xs

  ex₁ : 1 ∈ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ex₁ = it  -- overlapping instances

However, *if* we looked for the appropriate arguments *before* checking
for overlap, the goal above would have a unique solution. The
:option:`--backtracking-instance-search` option controls whether
instance arguments *to instances* should be filled in before checking
whether the instance is applicable.

.. warning::

  Agda uses naïve backtracking to check instances' constraints, which
  has exponential performance in the worst case. Enabling
  :option:`--backtracking-instance-search` might cause significant
  slowdown in instance search, and even apparent infinite loops.

.. _instance-resolution:

Instance resolution
-------------------

This section provides a precise specification of the instance resolution
algorithm.

Verify the goal
  The first step is checking that the goal type has the right shape to
  be solved by instance resolution.

  Instance search can only solve goals of the form ``{Γ} → C vs``, where
  the target type ``C`` is either a variable, a data type, a record
  type, or a postulate; and ``{Γ}`` represents a sequence of implicit or
  instance arguments.

  If this is not the case, instance resolution fails with an error
  message.

Find candidates
  The second step is to compute a list of *initial candidates*.

  :ref:`Let-bound <let-and-where>` variables and top-level definitions
  in scope are candidates if they are defined in an ``instance`` block.

  Local variables, i.e. variables bound in lambdas, function types,
  left-hand sides, or module parameters, are candidates if they are
  bound as instance arguments, using ``{{ }}``.

  If a local variable has an :ref:`eta record <eta-expansion>` type,
  then any of its :ref:`instance fields <instance-fields>` are also
  considered as locals. Beware that if Agda can not tell whether or not
  a local variable is eta-expandable (e.g., its type is a metavariable),
  instance search will not run.

  Only candidates of type ``{Δ} → C us``, where ``C`` is the target type
  computed in the previous stage, and ``{Δ}`` only contains implicit or
  instance arguments, are considered.

Check the type of the candidates
  The list of initial candidates is an overapproximation to the set of
  possible solutions. The next step is to check, in turn, whether the
  candidate could actually be used to solve the instance goal. If our
  goal is of the form ``{Γ} → C vs``, we take the following steps:

  #. The local context is extended by ``{Γ}``. This may bring additional
     candidates into scope.

  #. The candidate's type, say ``c : {Δ} → A``, is instantiated with
     fresh metavariables, say ``α``.

  #. The target type ``C vs`` is unified with ``A[α/Δ]``. If this results
     in a definite mismatch, the candidate is discarded.

  #. Finally, if :option:`--backtracking-instance-search` is enabled, we
     recursively apply instance search to any instance variables present
     in ``Δ``.

  If all of these steps succeed, we make note of the term ``λ {Γ} → c
  {α}`` as a potential solution.

Resolve overlaps
  The previous step might have left us with multiple potential
  solutions, even if recursive instance search was enabled. We now
  remove any potential solutions which are overlapped by a *strictly
  more specific* candidate.

  To wit, given a pair of candidates ``c1 : {Δ} → C xs`` and ``c2 : {Γ}
  → C ys``, we remove ``c1`` from the list exactly when:

  * There exists a substitution for the variables in ``Δ``, in terms of
    those in ``Γ``, which makes ``C xs`` and ``C ys`` definitionally
    equal. We say ``c2`` is *more specific* than ``c1``.

  * Such a substitution does *not* exist for ``Γ`` in terms of ``Δ``.
    This makes ``c2`` *strictly* more specific than ``c1``.

  * Either ``c1`` is overlappable or ``c2`` is overlapping. Keep in mind
    that instances marked ``OVERLAPS`` (or ``INCOHERENT``) are both
    overlappable and overlapping.

Compute the result
  After resolving overlaps, we may be in five situations:

  * There is exactly one non-incoherent candidate, along with some
    number of incoherent candidates. The non-incoherent candidate is
    chosen.

  * All the potential solutions are incoherent. Agda makes an arbitrary
    choice.

  * There are multiple candidates, and they all come from :ref:`instance
    fields <instance-fields>` which are marked with the ``overlap``
    keyword. Agda again makes an arbitrary choice.

  * There are multiple, non-incoherent candidates. The instance
    constraint is postponed until we have more information available
    about either the goal or the candidates.

  * There are no candidates at all. This is an immediate error.

  If there are left-over instance problems at the end of type checking,
  the corresponding metavariables are printed in the Emacs status
  buffer, together with their types and source location. The candidates
  that gave rise to potential solutions can be printed with the
  :ref:`show constraints command <emacs-global-commands>` (``C-c C-=``).
