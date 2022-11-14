..
  ::
  module language.sort-system where

  open import Agda.Builtin.Unit

.. _sort-system:

***********
Sort System
***********

.. _intro-sorts:

Sorts (also known as universes) are types whose members themselves are
again types. The fundamental sort in Agda is named ``Set`` and it
denotes the universe of small types. But for some applications, other
sorts are needed. This page explains the need for additional sorts and
describes all the sorts that are used by Agda.


..
  ::
  module Monomorphic where

Introduction to universes
=========================

Russell's paradox implies that the collection of all sets is not
itself a set. Namely, if there were such a set ``U``, then one could
form the subset ``A ⊆ U`` of all sets that do not contain
themselves. Then we would have ``A ∈ A`` if and only if ``A ∉ A``, a
contradiction.

Likewise, Martin-Löf’s type theory had originally a rule ``Set : Set``
but Girard showed that it is inconsistent.  This result is known as
Girard’s paradox. Hence, not every Agda type is a ``Set``. For
example, we have

.. code-block:: agda

    Bool : Set
    Nat : Set

but not ``Set : Set``. However, it is often convenient for ``Set`` to
have a type of its own, and so in Agda, it is given the type ``Set₁``:

.. code-block:: agda

    Set : Set₁

In many ways, expressions of type ``Set₁`` behave just like
expressions of type ``Set``; for example, they can be used as types of
other things. However, the elements of ``Set₁`` are potentially
*larger*; when ``A : Set₁``, then ``A`` is sometimes called a **large
set**. In turn, we have

.. code-block:: agda

    Set₁ : Set₂
    Set₂ : Set₃

and so on. A type whose elements are types is called a **sort** or a
**universe**; Agda provides an infinite number of universes ``Set``,
``Set₁``, ``Set₂``, ``Set₃``, ..., each of which is an element of the
next one. In fact, ``Set`` itself is just an abbreviation for
``Set₀``. The subscript ``n`` is called the **level** of the universe
``Setₙ``.

.. note:: You can also write ``Set1``, ``Set2``, etc., instead of
  ``Set₁``, ``Set₂``. To enter a subscript in the Emacs mode, type
  "``\_1``".


Universe example
----------------

So why are universes useful? Because sometimes it is necessary to
define, and prove theorems about, functions that operate not just on
sets but on large sets. In fact, most Agda users sooner or later
experience an error message where Agda complains that ``Set₁ !=
Set``. These errors usually mean that a small set was used where a
large one was expected, or vice versa.

For example, suppose you have defined the usual datatypes for lists
and cartesian products:

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

There is only one small problem with this definition. The type of
``Prod`` should be

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

Universe polymorphism
---------------------

To allow definitions of functions and datatypes that work for all
possible universes ``Setᵢ``, Agda provides a type ``Level`` of
universe levels and level-polymorphic universes ``Set ℓ`` where ``ℓ :
Level``. For more information, see the page on :ref:`universe levels
<universe-levels>`.

Agda's sort system
==================

The implementation of Agda’s sort system is closely based on the
theory of pure type systems.  The full sort system of Agda consists of
the following sorts:

- ``Setᵢ`` and its universe-polymorphic variant ``Set ℓ``
- ``Propᵢ`` and its universe-polymorphic variant ``Prop ℓ``
- ``Setωᵢ``


Sorts ``Setᵢ`` and ``Set ℓ``
----------------------------

As explained in the introduction, Agda has a hierarchy of sorts ``Setᵢ
: Setᵢ₊₁``, where ``i`` is any concrete natural number, i.e. ``0``,
``1``, ``2``, ``3``, ... The sort ``Set`` is an abbreviation for
``Set₀``.

You can also refer to these sorts with the alternative syntax
``Seti``.  That means that you can also write ``Set0``, ``Set1``,
``Set2``, etc., instead of ``Set₀``, ``Set₁``, ``Set₂``.

In addition, Agda supports the universe-polymorphic version ``Set ℓ``
where ``ℓ : Level`` (see :ref:`universe levels <universe-levels>`).


Sorts ``Propᵢ`` and ``Prop ℓ``
------------------------------

In addition to the hierarchy ``Setᵢ``, Agda also supports a second
hierarchy ``Propᵢ : Setᵢ₊₁`` (or ``Propi``) of :ref:`proof-irrelevant
propositions <prop>`. Like ``Set``, ``Prop`` also has a
universe-polymorphic version ``Prop ℓ`` where ``ℓ : Level``.


.. _set-omega-plus-n:

Sorts ``Setωᵢ``
---------------

To assign a sort to types such as ``(ℓ : Level) → Set ℓ``, Agda
further supports an additional sort ``Setω`` that stands above all
sorts ``Setᵢ``.

Just as for ``Set`` and ``Prop``, ``Setω`` is the lowest level at an
infinite hierarchy ``Setωᵢ : Setωᵢ₊₁`` where ``Setω = Setω₀``. You can
also refer to these sorts with the alternative syntax ``Setωi``.  That
means that you can also write ``Setω0``, ``Setω1``, ``Setω2``, etc.,
instead of ``Setω₀``, ``Setω₁``, ``Setω₂``.

Now it is allowed, for instance, to declare a datatype in ``Setω``.
This means that ``Setω`` before the implementation of this hierarchy,
``Setω`` used to be a term, and there was no bigger sort than it in
Agda.  Now a type can be assigned to it, in this case, ``Setω₁``.

However, unlike the standard hierarchy of universes ``Setᵢ``, this
second hierarchy ``Setωᵢ`` does not support universe
polymorphism. This means that it is not possible to quantify over
*all* Setωᵢ at once. For example, the expression ``∀ {i} (A : Setω i)
→ A → A`` would not be a well-formed agda term. See the section
on ``Setω`` on the page on :ref:`universe levels <set-omega>` for more
information.

Concerning other applications, It should not be necessary to refer to
these sorts during normal usage of Agda, but they might be useful for
defining :ref:`reflection-based macros <macros>`.


.. note:: When :option:`--omega-in-omega` is enabled, ``Setωᵢ`` is
  considered to be equal to ``Setω`` for all ``i`` (thus rendering
  Agda inconsistent).



Sort metavariables and unknown sorts
====================================

Under universe polymorphism, levels can be arbitrary terms, e.g., a
level that contains free variables. Sometimes, we will have to check
that some expression has a valid type without knowing what sort it has.
For this reason, Agda’s internal representation of sorts implements a constructor (sort
metavariable) representing an unknown sort. The constraint solver can
compute these sort metavariables, just like it does when computing
regular term metavariables.

However, the presence of sort metavariables also means that sorts of
other types can sometimes not be computed directly. For this reason,
Agda's internal representation of sorts includes three additional
constructors ``funSort``, ``univSort``, and ``piSort``. These
constructors compute to the proper sort once enough metavariables in
their arguments have been solved.

.. note::
   ``funSort``, ``univSort`` and ``piSort`` are *internal* constructors
   that may be printed when evaluating a term. The user can not enter
   them, nor introduce them in agda code. All these constructors do
   not represent new sorts but instead, they compute to the right sort
   once their arguments are known.


.. _funSort:

funSort
-------

The constructor ``funSort`` computes the sort of a function type
even if the sort of the domain and the sort of the codomain are still
unknown.

To understand how ``funSort`` works in general, let us assume the following
scenario:

* ``sA`` and ``sB`` are two (possibly different) sorts.
* ``A : sA``, meaning that ``A`` is a type that has sort ``sA``.
* ``B : sB``, meaning that ``B`` is a (possibly different) type that has
  sort ``sB``.

Under these conditions, we can build the function type
``A → B : funSort sA sB``. This type signature means that the function type
``A → B`` has a (possibly unknown) but well-defined sort ``funSort sA sB``,
specified in terms of the sorts of its domain and codomain.

If ``sA`` and ``sB`` happen to be known, then ``funSort sA sB`` can be computed
to a sort value. We list below all the possible computations that ``funSort``
can perform:

.. code-block:: agda

  funSort Setωᵢ    Setωⱼ    = Setωₖ            (where k = max(i,j))
  funSort Setωᵢ    (Set b)  = Setωᵢ
  funSort Setωᵢ    (Prop b) = Setωᵢ
  funSort (Set a)  Setωⱼ    = Setωⱼ
  funSort (Prop a) Setωⱼ    = Setωⱼ
  funSort (Set a)  (Set b)  = Set (a ⊔ b)
  funSort (Prop a) (Set b)  = Set (a ⊔ b)
  funSort (Set a)  (Prop b) = Prop (a ⊔ b)
  funSort (Prop a) (Prop b) = Prop (a ⊔ b)

Example: the sort of the function type ``∀ {A} → A → A`` with normal form
``{A : _5} → A → A`` evaluates to ``funSort (univSort _5) (funSort _5 _5)``
where:

* ``_5`` is a metavariable that represents the sort of ``A``.
* ``funSort _5 _5`` is the sort of ``A → A``.


.. note:: ``funSort`` can admit just two arguments, so it will be
  iterated when the function type has multiple arguments. E.g. the
  function type ``∀ {A} → A → A → A`` evaluates to ``funSort (univSort
  _5) (funSort _5 (funSort _5 _5))``

.. _univSort: agda

univSort
--------

``univSort`` returns the successor sort of a given sort.

Example: the sort of the function type ``∀ {A} → A`` with normal form
``{A : _5} → A`` evaluates to ``funSort (univSort _5) _5`` where:

* ``univSort _5`` is the sort where the sort of ``A`` lives, ie. the
  successor level of ``_5``.

We list below all the possible computations that ``univSort`` can perform:

.. code-block:: agda

  univSort (Set a)  = Set (lsuc a)
  univSort (Prop a) = Set (lsuc a)
  univSort Setωᵢ    = Setωᵢ₊₁

.. _piSort:

piSort
------

Similarly, ``piSort s1 s2`` is a constructor that computes the sort of
a Π-type given the sort ``s1`` of its domain and the sort ``s2`` of its
codomain as arguments.

To understand how ``piSort`` works in general, we set the following scenario:

* ``sA`` and ``sB`` are two (possibly different) sorts.
* ``A : sA``, meaning that ``A`` is a type that has sort ``sA``.
* ``x : A``, meaning that ``x`` has type ``A``.
* ``B : sB``, meaning that ``B`` is a type (possibly different than ``A``) that
  has sort ``sB``.

Under these conditions, we can build the dependent function type
``(x : A) → B : piSort sA (λ x → sB)``. This type signature means that the
dependent function type ``(x : A) → B`` has a (possibly unknown) but
well-defined sort ``piSort sA sB``, specified in terms of the element
``x : A`` and the sorts of its domain and codomain.

We list below all the possible computations that ``piSort`` can perform:

.. code-block:: agda

  piSort s1       (λ x → s2) = funSort s1 s2          (if x does not occur freely in s2)
  piSort (Set ℓ)  (λ x → s2) = Setω                   (if x occurs rigidly in s2)
  piSort (Prop ℓ) (λ x → s2) = Setω                   (if x occurs rigidly in s2)
  piSort Setωᵢ    (λ x → s2) = Setωᵢ                  (if x occurs rigidly in s2)

With these rules, we can compute the sort of the function type ``∀ {A}
→ ∀ {B} → B → A → B`` (or more explicitly, ``{A : _9} {B : _7} → B → A
→ B``) to be ``piSort (univSort _9) (λ A → funSort (univSort _7)
(funSort _7 (funSort _9 _7)))``

More examples:

* ``piSort Level (λ l → Set l)`` evaluates to ``Setω``
* ``piSort (Set l) (λ _ → Set l')`` evaluates to ``Set (l ⊔ l')``
* ``univSort (Set l)`` evaluates to ``Set (lsuc l)``
* ``piSort s (λ x -> Setωi)`` evaluates to ``funSort s Setωi``
