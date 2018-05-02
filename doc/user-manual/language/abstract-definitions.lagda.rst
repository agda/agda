..
  ::
  -- {-# OPTIONS --allow-unsolved-metas #-}
  module language.abstract-definitions where

  open import language.built-ins

.. _abstract-definitions:

********************
Abstract definitions
********************

Definitions can be marked as abstract, for the purpose of hiding
implementation details, or to speed up type-checking of other parts.
In essence, abstract definitions behave like postulates, thus, do not
reduce/compute.  For instance, proofs whose content does not matter
could be marked abstract, to prevent Agda from unfolding them (which
might slow down type-checking).

As a guiding principle, all the rules concerning ``abstract`` are
designed to prevent the leaking of implementation details of abstract
definitions.  Similar concepts of other programming language include
(non-representative sample):
UCSD Pascal's and Java's interfaces and ML's signatures.
(Especially when abstract definitions are used in combination with modules.)

Synopsis
--------

* Declarations can be marked as abstract using the block keyword ``abstract``.

* Outside of abstract blocks, abstract definitions do not reduce, they are treated as postulates,
  in particular:

  * Abstract functions never match, thus, do not reduce.

  * Abstract data types do not expose their constructors.

  * Abstract record types do not expose their fields nor constructor.

  * Other declarations cannot be abstract.

* Inside abstract blocks, abstract definitions reduce while type checking definitions,
  but not while checking their type signatures.
  Otherwise, due to dependent types, one could leak implementation
  details (e.g. expose reduction behavior by using propositional
  equality).

* Inside ``private`` type signatures in ``abstract`` blocks, abstract
  definitions do reduce. However, there are some problems with this. See `Issue
  #418 <https://github.com/agda/agda/issues/418#issuecomment-245590857>`_.

* The reach of the ``abstract`` keyword block extends recursively to
  the ``where``-blocks of a function and the declarations inside of a
  ``record`` declaration, but not inside modules declared in an
  abstract block.

Examples
--------

Integers can be implemented in various ways, e.g. as difference of two
natural numbers::

  module Integer where

    abstract

      ℤ = Nat × Nat

      0ℤ : ℤ
      0ℤ = 0 , 0

      1ℤ : ℤ
      1ℤ = 1 , 0

      _+ℤ_ : (x y : ℤ) → ℤ
      (p , n) +ℤ (p' , n') = (p + p') , (n + n')

      -ℤ_ : ℤ → ℤ
      -ℤ (p , n) = (n , p)

      _≡ℤ_ : (x y : ℤ) → Set
      (p , n) ≡ℤ (p' , n') = (p + n') ≡ (p' + n)

      private
        postulate
          +comm : ∀ n m → (n + m) ≡ (m + n)

      invℤ : ∀ x → (x +ℤ (-ℤ x)) ≡ℤ 0ℤ
      invℤ (p , n) rewrite +comm (p + n) 0 | +comm p n = refl

Using ``abstract`` we do not give away the actual representation of
integers, nor the implementation of the operations.  We can construct
them from ``0ℤ``, ``1ℤ``, ``_+ℤ_``, and ``-ℤ``, but only reason about
equality ``≡ℤ`` with the provided lemma ``invℤ``.

The following property ``shape-of-0ℤ`` of the integer zero exposes the
representation of integers as pairs.  As such, it is rejected by Agda:
when checking its type signature, ``proj₁ x`` fails to type check
since ``x`` is of abstract type ``ℤ``.  Remember that the abstract
definition of ``ℤ`` does not unfold in type signatures, even when in
an abstract block!  However, if we make ``shape-of-ℤ`` private,
unfolding of abstract definitions like ``ℤ`` is enabled, and we
succeed::

  -- A property about the representation of zero integers:

    abstract
      private
        shape-of-0ℤ : ∀ (x : ℤ) (is0ℤ : x ≡ℤ 0ℤ) → proj₁ x ≡ proj₂ x
        shape-of-0ℤ (p , n) refl rewrite +comm p 0 = refl

By requiring ``shape-of-0ℤ`` to be private to type-check, leaking of
representation details is prevented.

Scope of abstraction
--------------------

In child modules,
when checking an abstract definition,
the abstract definitions of the parent module are transparent::

  module M1 where
    abstract
      x = 0

    module M2 where
      abstract
        x-is-0 : x ≡ 0
        x-is-0 = refl

Thus, child modules can see into the representation choices of their
parent modules.  However, parent modules cannot see like this into
child modules, nor can sibling modules see through each others abstract
definitions. An exception to this is anonymous modules, which share
abstract scope with their parent module, allowing parent or sibling
modules to see inside their abstract definitions.

The reach of the ``abstract`` keyword does not extend into modules::

  module Parent where
    abstract
      module Child where
        y = 0
      x = 0  -- to avoid "useless abstract" error

    y-is-0 : Child.y ≡ 0
    y-is-0 = refl

The declarations in module ``Child`` are not abstract!

Abstract definitions with where-blocks
--------------------------------------

Definitions in a ``where`` block of an abstract definition are abstract
as well.  This means, they can see through the abstractions of their
uncles::

  module Where where
    abstract
      x : Nat
      x = 0
      y : Nat
      y = x
        where
        x≡y : x ≡ 0
        x≡y = refl

Type signatures in ``where`` blocks are private, so it is fine to make
type abbreviations in ``where`` blocks of abstract definitions::

  module WherePrivate where
    abstract
      x : Nat
      x = proj₁ t
        where
        T = Nat × Nat
        t : T
        t = 0 , 1
        p : proj₁ t ≡ 0
        p = refl

Note that if ``p`` was not private, application ``proj₁ t`` in its type
would be ill-formed, due to the abstract definition of ``T``.

Named ``where``-modules do not make their declarations private, thus
this example will fail if you replace ``x``'s ``where`` by ``module M
where``.
