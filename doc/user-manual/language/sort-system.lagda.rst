..
  ::
  module language.sort-system where

.. _sort-system:

***********
Sort System
***********

.. _intro-sorts:

Agda's sort system
-------------------

The implementation of Agda’s sort system is closely based on the theory
of pure type systems. Sorts (aka universes) are types whose members
themselves are again types. The fundamental sort in Agda is named ``Set``
and it denotes the universe of small types.

But for some applications, other sorts are needed. Martin-Löf’s type theory
had originally a rule ``Set : Set`` but Girard showed that it is inconsistent.
This result is known as Girard’s paradox. Agda implements an
:ref:`infinite hierarchy of universes <universe-levels>` that avoids this
inconsistency.

Under universe polymorphism, levels can be arbitrary terms, e.g., a
level that contains free variables. Sometimes, we will have to check
that some expression has a valid type without knowing what sort it has.

.. note::
   ``funSort``, ``univSort`` and ``piSort`` are *internal* constructors
   that may be printed when evaluating a term. The user can not enter them,
   nor introduce them in agda code.

.. _funSort:

funSort
-------

Agda’s internal representation of sorts implements a constructor (sort
metavariable) representing an unknown sort. The constraint solver can
compute these sort metavariables, just like it does when computing
regular term metavariables.

But this sort metavariable needs other constructors to solve function
types. The constructor ``funSort`` computes the sort of a function type
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

.. code-block::

  funSort Setω     _        = Setω
  funSort _        Setω     = Setω
  funSort (Set a)  (Set b)  = Set (a ⊔ b)
  funSort (Prop a) (Set b)  = Set (a ⊔ b)
  funSort (Set a)  (Prop b) = Prop (a ⊔ b)
  funSort (Prop a) (Prop b) = Prop (a ⊔ b)

Example: the sort of the function type ``∀ {A} → A → A`` with normal form
``{A : _5} → A → A`` evaluates to ``funSort (univSort _5) (funSort _5 _5)``
where:

* ``_5`` is a metavariable that represents the sort of ``A``.
* ``funSort _5 _5`` is the sort of ``A → A``.

Note that ``funSort`` can admit just two arguments, so it will be iterated
when the function type has multiple arguments. E.g. the function type
``∀ {A} → A → A → A`` evaluates to
``funSort (univSort _5) (funSort _5 (funSort _5 _5))``

.. _univSort:

univSort
--------

``univSort`` returns the successor sort of a given sort.

Example: the sort of the function type ``∀ {A} → A`` with normal form
``{A : _5} → A`` evaluates to ``funSort (univSort _5) _5`` where:

* ``univSort _5`` is the sort where the sort of ``A`` lives, ie. the
  successor level of ``_5``.

Note that ``univSort`` appled to ``Setω`` is well-defined only if the option
``--omega-in-omega`` is enabled in the agda file.

We list below all the possible computations that ``univSort`` can perform:

.. code-block::

  univSort (Set a)  = Set (lsuc a)
  univSort (Prop a) = Set (lsuc a)
  univSort Setω     = Setω                      (only if --omega-in-omega is enabled)

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

.. code-block::

  piSort s1 (λ x → s2) = funSort s1 s2          (if x does not occur freely in s2)
  piSort s1 (λ x → s2) = Setω                   (if x occurs freely in s2)

All these constructors do not represent new sorts but instead, they compute
to the right sort once their arguments are known.

More examples:

* ``piSort Level (λ l → Set l)`` evaluates to ``Setω``
* ``piSort (Set l) (λ _ → Set l')`` evaluates to ``Set (l ⊔ l')``
* ``univSort (Set l)`` evaluates to ``Set (lsuc l)``
* The function type ``∀ {A} → ∀ {B} → B → A → B`` with normal form
  ``{A : _9} {B : _7} → B → A → B`` evaluates to
  ``piSort (univSort _9) (λ A → funSort (univSort _7)
  (funSort _7 (funSort _9 _7)))``

Note that ``funSort`` and ``piSort`` are total functions on sort. But
``univSort`` is not always well-defined. Eg. without adding the
``--omega-in-omega`` option, ``Setω`` does not have a ``univSort``
(successor sort) since there is currently no next sort to ``Setω``.
Any uses of ``univSort`` will lead to a 'has bigger sort' constraint that
ensures the argument is not ``Setω``.

.. _set-omega-plus-n:

Sorts ``Setωᵢ``
---------------

Agda implements sorts of the form ``Setωᵢ``, being ``i`` any natural number,
i.e. ``0``, ``1``, ``2``, ``3``, ...

.. note::
   In particular, ``i`` can *not* be an arbitrary expression of type ``Nat``;
   therefore, ``Setωi`` cannot depend on any variables. This is an intentional
   design decision. Allowing it would require a new universe ``Set2ω``, which
   would then naturally lead to ``Set2ω+1``, and so on. Restricting ``i`` to
   just literal natural numbers avoids such an undesired circumstance.

The constructors ``funSort``, ``univSort``, and ``piSort`` that we saw in
the previous sections also work for ``Setωi``, but with this restriction
in mind. For example, ``piSort s` (λ x -> Setωi)`` will always reduce to
``funSort s Setωi`` since there is no way for the ``i`` to depend on the
variable ``x``.

The family of sorts ``Setωᵢ`` (aka ``Setω+n``) constitute a second hierarchy
``Setωᵢ : Setωᵢ₊₁`` where each sort has the type of its successor. This
mechanism is similar to the one implemented in the standard hierarchy
``Setᵢ : Setᵢ₊₁`` that we introduced in the section
:ref:`Universe Levels <universe-levels>`.

But, unlike the standard hierarchy of universes ``Setᵢ``, this second
hierarchy ``Setωᵢ`` does not support universe polymorphism. This means that
it is not possible to quantify over *all* Setω+n at once. For example, the
expression ``∀ {i} (A : Setω i) → A → A`` would not be a well-formed agda
term.

You can also refer to these sorts with the alternative syntax ``Setωi``.
That means that you can also write ``Setω0``, ``Setω1``, ``Setω2``, etc.,
instead of ``Setω₀``, ``Setω₁``, ``Setω₂``. To enter the subscript ``₁`` in
the Emacs mode, type "``\_1``".

The sort formerly known as ``Setω`` becomes now just an abbreviation for
``Setω₀``. Now it is allowed, for instance, to declare a datatype in ``Setω``.
This means that ``Setω`` before the implementation of this hierarchy,
``Setω`` used to be a term, and there was no bigger sort that it in Agda.
Now a type can be assigned to it, in this case, ``Setω₁``.

Concerning other applications,  It should not be necessary to refer to these
sorts during normal usage of Agda, but they might be useful for defining
:ref:`reflection-based macros <macros>`.
