
.. _smart-with:

**********
Smart with
**********


"Smart with" is an experimental alternative version of
:doc:`with-abstraction <with-abstraction>`
and :ref:`the rewrite construction <with-rewrite>`, enabled under the
``--smart-with`` flag.
Smart with fixes many
failure cases of ordinary with-abstractions, including
:ref:`ill-typed with-abstraction errors <ill-typed-with-abstractions>`.
The feature is inspired by the Altenkirch et al.'s
`"smart case" <https://shonan.nii.ac.jp/archives/seminar/007/files/2011/09/altenkirch_slides.pdf>`_ proposal.

Under the hood, smart with uses :doc:`local rewrite rules <local-rewriting>`
instead of :ref:`generalisation <generalisation>`. In this way, smart with
definitionally "remembers" the equality between the with-abstracted term
and the new argument.

Because smart with affects definitional equality, it is a non-trivial
extension to Agda's core theory.
To retain nice typechecking properties (transitivity and decidability of
definitional equality), a few
:ref:`restrictions <restrictions>` are placed on
smart with rewrites. However,
even under these restrictions, it is currently unknown whether smart with
is conservative ``--without-K``, or indeed is consistent with univalence.

Smart with by example
---------------------

::

  {-# OPTIONS --guardedness --smart-with #-}

  module language.smart-with where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite

..
  ::

  open import Agda.Builtin.Unit
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Bool
  open import Agda.Builtin.List

  data ⊥ : Set where

  cong : ∀ {A B : Set} {x y} (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  subst : ∀ {A : Set} {x y} (P : A → Set) → x ≡ y → P x → P y
  subst P refl d = d

  not : Bool → Bool
  not true  = false
  not false = true

  _∧_ : Bool → Bool → Bool
  true  ∧ b = b
  false ∧ b = false

As with plain Agda, smart with allows defining functions but scrutinising
the results of intermediary computations. For example, we can implement
``filter`` by with-abstracting over the result of applying the predicate to each
element of the list.

..
  ::

  module Filter where

::

    variable
      A : Set

    filter : (A → Bool) → List A → List A
    filter p  []       = []
    filter p  (x ∷ xs) with p x
    ... | true  = x ∷ filter p xs
    ... | false = filter p xs

Smart with diverges form plain with-abstraction in how it refines the
goal type/context. Plain with-abstraction performs a one-off generalisation
procedure, which means it can miss occurrences of the abstracted term if
they only appear after further pattern matching or function applications.

For example, when proving that filtering a list twice with the same predicate
is the same as filtering once, ordinary with-abstraction fails.
In the ``true`` branch, the inner ``filter p (x ∷ xs)`` on the left-hand side
reduces to ``x ∷ filter p xs``, but the outer ``filter`` remains stuck on
``p x``. With-abstraction "forgets" that ``p x`` is equal to ``true``!

Smart with "remembers" the connection between ``p x`` and ``true``
in the form of a local rewrite rule, enabling a simple ``filter-filter``
proof.

::

    filter-filter : ∀ p (xs : List A) → filter p (filter p xs) ≡ filter p xs
    filter-filter p []       = refl
    filter-filter p (x ∷ xs) with p x
    ... | true  = cong (x ∷_) (filter-filter p xs)
    ... | false = filter-filter p xs

The :ref:`inspect idiom <the-inspect-idiom>` provides an alternative way to
work around problems like this, but can be much more tedious in practice
(the provided with-abstraction equality is only propositional).

For another example, consider defining addition for following definition of
conatural numbers.

..
  ::

  module Conat where

::

    T : Bool → Set
    T true  = ⊤
    T false = ⊥

    record Conat : Set where
      coinductive
      field
        zero?  : Bool
        pred   : T (not zero?) → Conat
    open Conat public

To define the predecessor of ``n + m``, we first scrutinise ``n .zero?``.
In the ``false`` case, we need
to take the predecessor of ``n``, and therefore provide evidence that
``n`` is indeed non-zero (``T (not (n .zero?))``).

Smart with "remembers" that ``n .zero?`` is ``false`` and so enables simply
passing ``tt`` here.

::

    _+_ : Conat → Conat → Conat
    (n + m) .zero? = n .zero? ∧ m .zero?
    (n + m) .pred p with n .zero?
    ... | true  = m .pred p
    ... | false = n .pred tt + m

Finally we note that smart with/rewrite does not encounter
:ref:`ill-typed with-abstraction errors <ill-typed-with-abstractions>`.
For example, consider concatenation of length-indexed vectors.

..
  ::

  module Ve,cExample where
    open import Agda.Builtin.Nat

    variable
      A : Set

::

    variable
      n m : Nat

    data Vec (A : Set) : Nat → Set where
      []  : Vec A zero
      _∷_ : A → Vec A n → Vec A (suc n)

    _++_ : Vec A n → Vec A m → Vec A (n + m)
    []       ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)


To prove the ``[]`` is a right-identity of vector concatenation, we
first need to prove that ``zero`` is a right-identity of addition.
Using smart with, we can simply rewrite over the identity proof.
Ordinary with-abstraction instead hits an error here (generalisation
produces an ill-typed context).

::

    +zero : (n : Nat) → n + zero ≡ n
    +zero zero    = refl
    +zero (suc n) = cong suc (+zero n)

    ++[] : (xs : Vec A n) → subst (Vec A) (+zero n) (xs ++ []) ≡ xs
    ++[]             []
      = refl
    ++[] {n = suc n} (x ∷ xs)
      rewrite +zero n
      = cong (x ∷_) (++[] xs)

.. _restrictions:

Restrictions
------------

To retain nice typechecking properties (transitivity and decidability of
definitional equality), we place some restrictions on smart
with/rewrite. Specifically, the local rewrite rules
introduced by with-abstractions/rewrites must satisfy the below criteria:

- The left-hand side must be neutral (not constructor-headed or underapplied).

- Right-hand side must not contain closures (i.e. lambdas or underapplied
  functions, not underneath a stuck application).

- The left-hand side may not occur in the right-hand side or any previous
  ``--smart-with`` rewrite.

`Typechecking Local Equality Reflection <https://codeberg.org/NathanielB/reflection-paper/src/branch/main/paper.pdf>`_
proves decidability of definitional equality under these restrictions.
