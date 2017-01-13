..
  ::
  module language.instance-arguments where

  open import language.built-ins
    using (Bool; true; false; List; _∷_; []; Nat; _-_; zero; suc; _+_)
    renaming (_==_ to natEquals)

  open import Agda.Primitive

  postulate undefined : ∀ {u} {A : Set u} → A

.. _instance-arguments:

******************
Instance Arguments
******************

.. contents::
   :depth: 2
   :local:

Instance arguments are the Agda equivalent of Haskell type class constraints
and can be used for many of the same purposes. In Agda terms, they are
:ref:`implicit arguments <implicit-arguments>` that get solved by a special
`instance resolution`_ algorithm, rather than by the unification algorithm used
for normal implicit arguments. In principle, an instance argument is resolved,
if a unique *instance* of the required type can be built from `declared
instances <declaring instances_>`_ and the current context.

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

  it : ∀ {a} {A : Set a} {{_ : A}} → A
  it {{x}} = x

Note that instance arguments in types are always named, but the name can be ``_``:

.. code-block:: agda

  _==_ : {A : Set} → {{Eq A}} → A → A → Bool    -- INVALID

..
  ::
  module example-underscore (Eq : Set → Set) where

::

     _==_ : {A : Set} {{_ : Eq A}} → A → A → Bool  -- VALID

..
  ::
     _==_ = undefined

Defining type classes
~~~~~~~~~~~~~~~~~~~~~

The type of an instance argument must have the form ``{Γ} → C vs``, where ``C``
is a bound variable or the name of a data or record type, and ``{Γ}`` denotes
an arbitrary number of (ordinary) implicit arguments (see `dependent
instances`_ below for an example where ``Γ`` is non-empty). Other than that
there are no requirements on the type of an instance argument. In particular,
there is no special declaration to say that a type is a "type class". Instead,
Haskell-style type classes are usually defined as :ref:`record types
<record-types>`. For instance,

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

    mempty : ∀ {a} {A : Set a} {{_ : Monoid A}} → A
    _<>_   : ∀ {a} {A : Set a} {{_ : Monoid A}} → A → A → A

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


    mempty : ∀ {a} {A : Set a} {{_ : Monoid A}} → A
    mempty {{mon}} = Monoid.mempty mon

Although record types are a natural fit for Haskell-style type classes, you can
use instance arguments with data types to good effect. See the `examples`_ below.

Declaring instances
~~~~~~~~~~~~~~~~~~~

A seen above, instance arguments in the context are available when solving
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

  mconcat : ∀ {a} {A : Set a} {{_ : Monoid A}} → List A → A
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
      eqList : ∀ {a} {A : Set a} {{_ : Eq A}} → Eq (List A)
      _==_ {{eqList}} []       []       = true
      _==_ {{eqList}} (x ∷ xs) (y ∷ ys) = x == y && xs == ys
      _==_ {{eqList}} _        _        = false

      eqNat : Eq Nat
      _==_ {{eqNat}} = natEquals

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
   ``loop : ∀ {a} {A : Set a} {{_ : Eq A}} → Eq A``.
   To prevent looping in cases like this, the search depth of instance search
   is limited, and once the maximum depth is reached, a type error will be
   thrown. You can set the maximum depth using the ``--instance-search-depth``
   flag.

Constructor instances
+++++++++++++++++++++

Although instance arguments are most commonly used for record types, mimicking
Haskell-style type classes, they can also be used with data types. In this case
you often want the constructors to be instances, which is achieved by declaring
them inside an ``instance`` block. Typically arguments to constructors are not
instance arguments, so during instance resolution explicit arguments are
treated as instance arguments. See `instance resolution`_ below for the details.

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

  mkFin : ∀ {n} (m : Nat) {{_ : suc m - n ≡ 0}} → Fin n
  mkFin {zero}  m {{}}
  mkFin {suc n} zero    = zero
  mkFin {suc n} (suc m) = suc (mkFin m)

  five : Fin 6
  five = mkFin 5 -- OK

.. code-block: agda
  badfive : Fin 5
  badfive = mkFin 5 -- Error: No instance of type 1 ≡ 0 was found in scope.

In the first clause of ``mkFin`` we use an :ref:`absurd pattern
<absurd-patterns>` to discharge the impossible assumption ``suc m ≡ 0``.  See
the `next section <examples_>`_ for another example of constructor instances.

Record fields can also be declared instances, with the effect that the
corresponding projection function is considered a top-level instance.

Examples
~~~~~~~~

Proof search
++++++++++++

Instance arguments are useful not only for Haskell-style type classes, but they
can also be used to get some limited form of proof search (which, to be fair,
is also true for Haskell type classes). Consider the following type, which
models a proof that a particular element is present in a list as the index at
which the element appears::

  infix 4 _∈_
  data _∈_ {A : Set} (x : A) : List A → Set where
    instance
      zero : ∀ {xs} → x ∈ x ∷ xs
      suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

Here we have declared the constructors of ``_∈_`` to be instances, which allows
instance resolution to find proofs for concrete cases. For example,

::

  ex₁ : 1 + 2 ∈ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ex₁ = it  -- computes to suc (suc zero)

  ex₂ : {A : Set} (x y : A) (xs : List A) → x ∈ y ∷ y ∷ x ∷ xs
  ex₂ x y xs = it  -- suc (suc zero)

  ex₃ : {A : Set} (x y : A) (xs : List A) {{i : x ∈ xs}} → x ∈ y ∷ y ∷ xs
  ex₃ x y xs = it  -- suc (suc i)

It will fail, however, if there are more than one solution, since instance
arguments must be unique. For example,

.. code-block:: agda

  fail₁ : 1 ∈ 1 ∷ 2 ∷ 1 ∷ []
  fail₁ = it  -- ambiguous: zero or suc (suc zero)

  fail₂ : {A : Set} (x y : A) (xs : List A) {{i : x ∈ xs}} → x ∈ y ∷ x ∷ xs
  fail₂ x y xs = it -- suc zero or suc (suc i)

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
      eqΣ : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : Eq A}} {{_ : ∀ {x} → Eq (B x)}} → Eq (Σ A B)
      _==_ {{eqΣ}} (x , y) (x₁ , y₁) with x == x₁
      _==_ {{eqΣ}} (x , y) (x₁ , y₁)    | nothing = nothing
      _==_ {{eqΣ}} (x , y) (.x , y₁)    | just refl with y == y₁
      _==_ {{eqΣ}} (x , y) (.x , y₁)    | just refl    | nothing   = nothing
      _==_ {{eqΣ}} (x , y) (.x , .y)    | just refl    | just refl = just refl

Note that the instance argument for ``B`` states that there should be an ``Eq``
instance for ``B x``, for any ``x : A``. The argument ``x`` must be implicit,
indicating that it needs to be inferred by unification whenever the ``B``
instance is used. See `instance resolution`_ below for more details.

Instance resolution
-------------------

Given a goal that should be solved using instance resolution we proceed in the
following four stages:

Verify the goal
  First we check that the goal is not already solved. This can happen if there
  are :ref:`unification constraints <implicit-arguments>` determining the
  value, or if it is of singleton record type and thus solved by
  :ref:`eta-expansion <eta-expansion>`.

  Next we check that the goal type has the right shape to be solved by instance
  resolution. It should be of the form ``{Γ} → C vs``, where the target type
  ``C`` is a variable from the context or the name of a data or record type,
  and ``{Γ}`` denotes a telescope of implicit arguments. If this is not the
  case instance resolution fails with an error message\ [#issue1322]_.

  Finally we have to check that there are no *unconstrained*
  :ref:`metavariables <metavariables>` in ``vs``. A metavariable ``α`` is
  considered constrained if it appears in an argument that is determined by the
  type of some later argument, or if there is an existing constraint of the
  form ``α us = C vs``, where ``C`` inert (i.e. a data or type constructor).
  For example, ``α`` is constrained in ``T α xs`` if ``T : (n : Nat) → Vec A
  n → Set``, since the type of the second argument of ``T`` determines the value
  of the first argument. The reason for this restriction is that instance
  resolution risks looping in the presence of unconstrained metavariables. For
  example, suppose the goal is ``Eq α`` for some metavariable ``α``. Instance
  resolution would decide that the ``eqList`` instance was applicable if
  setting ``α := List β`` for a fresh metavariable ``β``, and then proceed to
  search for an instance of ``Eq β``.

Find candidates
  In the second stage we compute a set of *candidates*. :ref:`Let-bound
  <let-and-where>` variables and top-level definitions in scope are candidates if they
  are defined in an ``instance`` block. Lambda-bound variables, i.e. variables
  bound in lambdas, function types, left-hand sides, or module parameters, are
  candidates if they are bound as instance arguments using ``{{ }}``.
  Only candidates that compute something of type ``C us``, where ``C`` is the
  target type computed in the previous stage, are considered.

Check the candidates
  We attempt to use each candidate in turn to build an instance of the goal
  type ``{Γ} → C vs``. First we extend the current context by ``Γ``. Then,
  given a candidate ``c : Δ → A`` we generate fresh metavariables ``αs : Δ``
  for the arguments of ``c``, with ordinary metavariables for implicit
  arguments, and instance metavariables, solved by a recursive call to instance
  resolution, for explicit arguments and instance arguments.

  Next we :ref:`unify <unification>` ``A[Δ := αs]`` with ``C vs`` and apply
  instance resolution to the instance metavariables in ``αs``. Both unification
  and instance resolution have three possible outcomes: *yes*, *no*, or
  *maybe*. In case we get a *no* answer from any of them, the current candidate
  is discarded, otherwise we return the potential solution ``λ {Γ} → c αs``.

Compute the result
  From the previous stage we get a list of potential solutions. If the list is
  empty we fail with an error saying that no instance for ``C vs`` could be
  found (*no*). If there is a single solution we use it to solve the goal
  (*yes*), and if there are multiple solutions we check if they are all equal.
  If they are, we solve the goal with one of them (*yes*), but if they are not,
  we postpone instance resolution (*maybe*), hoping that some of the *maybes*
  will turn into *nos* once we know more about the involved metavariables.

  If there are left-over instance problems at the end of type checking, the
  corresponding metavariables are printed in the Emacs status buffer together
  with their types and source location. The candidates that gave rise to
  potential solutions can be printed with the :ref:`show constraints command
  <emacs-global-commands>` (``C-c C-=``).

.. [#issue1322] Instance goal verification is buggy at the moment. See `issue
   #1322 <https://github.com/agda/agda/issues/1322>`_.
