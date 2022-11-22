..
  ::
  {-# OPTIONS --rewriting --sized-types #-}
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

  Consequently information from checking the body of a definition cannot leak
  into its type signature, effectively disabling type inference for abstract
  definitions. This means that all abstract definitions need a complete type
  signature.

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

      ℤ : Set
      ℤ = Nat × Nat

      0ℤ : ℤ
      0ℤ = 0 , 0

      1ℤ : ℤ
      1ℤ = 1 , 0

      _+ℤ_ : (x y : ℤ) → ℤ
      (p , n) +ℤ (p' , n') = (p + p') , (n + n')

      _*ℤ_ : (x y : ℤ) → ℤ
      (a , b) *ℤ (c , d) = ((a * c) + (b * d)) , ((a * d) + (b * c))

      infixl 20 _+ℤ_
      infixl 30 _*ℤ_

      -ℤ_ : ℤ → ℤ
      -ℤ (p , n) = (n , p)

      _≡ℤ_ : (x y : ℤ) → Set
      (p , n) ≡ℤ (p' , n') = (p + n') ≡ (p' + n)

      infix 10 _≡ℤ_

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
an abstract block!  To work around this we have to define aliases for
the projections functions::

  -- A property about the representation of zero integers:

    abstract
      private
        posZ : ℤ → Nat
        posZ = proj₁

        negZ : ℤ → Nat
        negZ = proj₂

        shape-of-0ℤ : ∀ (x : ℤ) (is0ℤ : x ≡ℤ 0ℤ) → posZ x ≡ negZ x
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
      x : Nat
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
        y : Nat
        y = 0
      x : Nat
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

Unfolding control
-----------------

Agda (since 2.6.4) implements a form of unfolding control for abstract
definitions, where later abstract blocks (in possibly different modules)
can choose to reduce abstract definitions from earlier blocks.

For example, in a *different* module (here ``Integer-ring``), we could
prove equations (using the extensional equality ``_≡ℤ_``) expressing
that the type ``ℤ`` is a ring, for example distributivity of
multiplication over addition on the left::

  module Integer-ring where
    open Integer
    abstract unfolding (ℤ) where
      distlℤ : ∀ x y z → x *ℤ (y +ℤ z) ≡ℤ x *ℤ y +ℤ x *ℤ z
      distlℤ (a , b) (c , d) (e , f) = wow where postulate
        wow : a * (c + e) + b * (d + f) + (a * d + b * c + (a * f + b * e))
            ≡ a * c + b * d + (a * e + b * f) + (a * (d + f) + b * (c + e))

We've left the proof of the underlying equation on naturals as a
postulate, since it is best left for a semiring solver, but the point of
the example is that in an ``abstract unfolding (ℤ)`` block, we're
allowed to see that ``ℤ = Nat × Nat``, definitionally. Additionally, we
can unfold anything that is declared in the same ``abstract`` block as
one of the ``unfolding`` names, to keep subject reduction::

  module SR1 where
    abstract
      X : Set
      X = Nat

      val : X
      val = 123

  module SR2 where
    abstract unfolding (SR1.val) where
      val′ : Nat
      val′ = SR1.val

It'd be incorrect for us to unfold ``SR1.val`` to ``123 : Nat`` if we
don't have a definitional equality ``SR1.X = Nat``. This can also be
seen if we have a **chain** of unfolding blocks::

  module SR3 where abstract
    X : Set
    X = Nat

  module SR4 where abstract unfolding (SR3.X) where
    val : SR3.X
    val = 123

  module SR5 where abstract unfolding (SR4.val) where
    val′ : SR3.X
    val′ = 123
    -- Even though we only asked for SR4.val, we must also have SR3.XA

Note that ``unfolding`` declarations (intentionally) do not apply to the
**type signatures** in an abstract block, and you must use a helper
definition to cause the unfolding::

  module TySig where abstract unfolding (SR5.val′) where
    private
      ty : Set
      ty = SR5.val′ ≡ 123

    _ : ty
    _ = refl

In the definition above, it'd be illegal to write ``_ : SR5.val′ ≡
123``, since we do not unfold ``SR3.X = Nat`` **in the type signature**,
but that unfolding is required since the arguments to ``_≡_`` must have
the same type.
