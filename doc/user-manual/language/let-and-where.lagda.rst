..
  ::
  module language.let-and-where where

  open import language.built-ins



.. _let-and-where:

********************************
Local Definitions: let and where
********************************

There are two ways of declaring local definitions in Agda:

- let-expressions
- where-blocks

.. _let-expressions:

let-expressions
===============

A let-expression defines an abbreviation.
In other words, the expression that we define in a let-expression
can neither be recursive nor defined by pattern matching.

Example::

  f : Nat
  f = let h : Nat → Nat
          h m = suc (suc m)
      in  h zero + h (suc zero)

let-expressions have the general form

.. code-block:: agda

  let f₁ : A₁₁ → … → A₁ₙ → A₁
      f₁ x₁ … xₙ = e₁
      …
      fₘ : Aₘ₁ → … → Aₘₖ → Aₘ
      fₘ x₁ … xₖ = eₘ
  in  e’

where previous definitions are in scope in later definitions.  The
type signatures can be left out if Agda can infer them.
After type-checking, the meaning of this is simply the substitution
``e’[f₁ := λ x₁ … xₙ → e; …; fₘ := λ x₁ … xₖ → eₘ]``.  Since Agda
substitutes away let-bindings, they do not show up in terms Agda
prints, nor in the goal display in interactive mode.

where-blocks
============

where-blocks are much more powerful than let-expressions, as they
support arbitrary local definitions.
A ``where`` can be attached to any function clause.

where-blocks have the general form

.. code-block:: agda

  clause
    where
    decls

or

.. code-block:: agda


  clause
    module M where
    decls

A simple instance is

.. code-block:: agda

  g ps = e
    where
    f : A₁ → … → Aₙ → A
    f p₁₁ … p₁ₙ= e₁
    …
    …
    f pₘ₁ … pₘₙ= eₘ

Here, the ``pᵢⱼ`` are patterns of the corresponding types and ``eᵢ`` is an expression that can contain occurrences of ``f``.
Functions defined with a where-expression must follow the rules for general definitions by pattern matching.

Example::

  reverse : {A : Set} → List A → List A
  reverse {A} xs = rev-append xs []
    where
    rev-append : List A → List A → List A
    rev-append [] ys = ys
    rev-append (x ∷ xs) ys = rev-append xs (x ∷ ys)

Variable scope
--------------

The pattern variables of the parent clause of the where-block are in
scope; in the previous example, these are ``A`` and ``xs``.  The
variables bound by the type signature of the parent clause are not in
scope.  This is why we added the hidden binder ``{A}``.

Scope of the local declarations
-------------------------------

The ``where``-definitions are not visible outside of the clause that
owns these definitions (the parent clause).  If the ``where``-block is
given a name (form ``module M where``), then the definitions are
available as qualified by ``M``, since module ``M`` is visible even
outside of the parent clause.  The special form of an anonymous module
(``module _ where``) makes the definitions visible outside of the
parent clause without qualification.

If the parent function of a named ``where``-block
(form ``module M where``) is ``private``,
then module ``M`` is also ``private``.
However, the declarations inside ``M`` are not private unless declared
so explicitly.  Thus, the following example scope checks fine::

  module Parent₁ where
    private
      parent = local
        module Private where
        local = Set
    module Public = Private

  test₁ = Parent₁.Public.local

Likewise, a ``private`` declaration for a parent function does not
affect the privacy of local functions defined under a
``module _ where``-block::

  module Parent₂ where
    private
      parent = local
        module _ where
        local = Set

  test₂ = Parent₂.local

They can be declared ``private`` explicitly, though::

  module Parent₃ where
    parent = local
      module _ where
      private
        local = Set

Now, ``Parent₃.local`` is not in scope.

A ``private`` declaration for the parent of an ordinary
``where``-block has no effect on the local definitions, of course.
They are not even in scope.

Proving properties
==================

Sometimes one needs to refer to local definitions in proofs about the
parent function.  In this case, the ``module ⋯ where`` variant is preferable.

.. code-block:: agda


  reverse : {A : Set} → List A → List A
  reverse {A} xs = rev-append xs []
     module Rev where
     rev-append : List A → List A → List A
     rev-append [] ys = ys
     rev-append (x :: xs) ys = rev-append xs (x :: ys)

This gives us access to the local function as

.. code-block:: agda

  Rev.rev-append : {A : Set} (xs : List A) → List A → List A → List A

Alternatively, we can define local
functions as private to the module we are working in; hence, they
will not be visible in any module that imports this module but it will
allow us to prove some properties about them.

::

  private
     rev-append : {A : Set} → List A → List A → List A
     rev-append []        ys = ys
     rev-append (x ∷ xs) ys = rev-append xs (x ∷ ys)

  reverse' : {A : Set} → List A → List A
  reverse' xs = rev-append xs []

More Examples (for Beginners)
=============================

Using a let-expression::

  tw-map : {A : Set} → List A → List (List A)
  tw-map {A} xs = let twice : List A → List A
                      twice xs = xs ++ xs
                  in  map (\ x → twice [ x ]) xs

Same definition but with less type information::

  tw-map' : {A : Set} → List A → List (List A)
  tw-map' {A} xs = let twice : _
                       twice xs = xs ++ xs
                   in  map (\ x → twice [ x ]) xs

Same definition but with a where-expression

::

  tw-map'' : {A : Set} → List A → List (List A)
  tw-map'' {A} xs =  map (\ x → twice [ x ]) xs
     where twice : List A → List A
           twice xs = xs ++ xs

Even less type information using let::

  g : Nat → List Nat
  g zero    = [ zero ]
  g (suc n) = let sing = [ suc n ]
              in  sing ++ g n

Same definition using where::

  g' : Nat → List Nat
  g' zero = [ zero ]
  g' (suc n) = sing ++ g' n
     where  sing = [ suc n ]

More than one definition in a let::

  h : Nat → Nat
  h n = let add2 : Nat
            add2 = suc (suc n)

            twice : Nat → Nat
            twice m = m * m

        in twice add2

More than one definition in a where::

  fibfact : Nat → Nat
  fibfact n = fib n + fact n
   where fib : Nat → Nat
         fib zero = suc zero
         fib (suc zero) = suc zero
         fib (suc (suc n)) = fib (suc n) + fib n

         fact : Nat → Nat
         fact zero = suc zero
         fact (suc n) = suc n * fact n

Combining let and where::

  k : Nat → Nat
  k n = let aux : Nat → Nat
            aux m = pred (h m) + fibfact m
        in aux (pred n)
    where pred : Nat → Nat
          pred zero = zero
          pred (suc m) = m
