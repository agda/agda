..
  ::
  module sort.system where

.. _sort-system:

***********
Sort System
***********

.. _intro-sorts:

Agda's sorts system
-------------------

The implementation of Agda’s sorts system is closely based on the theory
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

funSort
-------

Agda’s internal representation of sorts implements a constructor (sort
metavariable) representing an unknown sort. The constraint solver can
compute these sort metavariables, just like it does when computing
regular term metavariables.

But this sort metavariable need other constructors to solve function
types. The constructor ``funSort`` computes the sort of a function type
even if the sort of the domain and the sort of the codomain are still
unknown. Here is how ``funSort`` behaves with all possible sorts:

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
* ``funSort _5 _5`` is the sort of ``A → A``

Note that ``funSort`` can admit just two arguments, so it will be iterated
when the function type has multiple arguments. E.g. the function type
``∀ {A} → A → A → A`` evaluates to
``funSort (univSort _5) (funSort _5 (funSort _5 _5))``

univSort
--------

`univSort`` returns the successor sort of a given sort.

* ``univSort _5`` is the sort where the sort of ``A`` lives, ie. the
  successor level of ``_5``.

``univSort`` appled to ``Setω`` is well-defined only if the option
``--omega-in-omega`` is enabled in the agda file.

.. code-block::

  univSort (Set a)  = Set (lsuc a)
  univSort (Prop a) = Set (lsuc a)
  univSort Setω     = Setω                      (only if --omega-in-omega is enabled)

PiSort
------

Similarly, ``PiSort s1 s2`` is a constructor that computes the sort of
a Π-type given the sort ``s1`` of its domain and the sort ``s2`` of its
codomain as arguments.

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

Note that ``funSort`` and ``PiSort`` are total functions on sort. But
``UnivSort`` is not always well-defined. Eg. without adding the
``--omega-in-omega`` option, ``Setω`` does not have a ``UnivSort``
(successor sort) since there is currently no next sort to ``Setω``.
Any uses of ``univSort`` will lead to a 'has bigger sort' constraint that
ensures the argument is not ``Setω``.
