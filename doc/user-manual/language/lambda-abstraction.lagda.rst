..
  ::
  {-# OPTIONS --erasure #-}

  module language.lambda-abstraction where

  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.List
  open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
  open import Agda.Builtin.Sigma

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y

  data ⊥ : Set where

  record Monoid (A : Set) : Set where
    field
      mempty : A
      mappend : A → A → A
  open Monoid {{...}}

  _×_ : (A B : Set) → Set
  A × B = Σ A λ _ → B

.. _lambda-abstraction:

******************
Lambda Abstraction
******************

.. _lambda-expressions:

Lambda expressions
------------------

Anonymous functions can be defined using a lambda expression ``\x → u``::

  myFun = \x → x + x -- equivalent: `myFun x = x + x`

You can also use the Unicode symbol ``λ`` (type “\\lambda” or “\\Gl” in the Emacs Agda mode) instead of ``\`` (type “\\\\” in the Emacs Agda mode).

Lambda expressions can take several arguments and arguments can optionally be
annotated with a type. For instance, both expressions below have type
``(A : Set) → A → A`` (the second expression checks against other types as
well):

..
  ::
  example₁ example₂ : (A : Set) (x : A) → A

::

  example₁ = \ (A : Set)(x : A) → x
  example₂ = \ A x → x

A functions taking ``n`` (> 1) arguments is equivalent to a function that takes
a single argument and returns another function with ``n-1`` arguments, i.e.
functions are curried.

::

  curry : (λ x y → x + y) ≡ (λ x → (λ y → x + y))
  curry = refl

All functions in Agda satisfy η-equality: ``f`` is (definitionally) equal to
``λ x → f x``.

::

  etaFun : myFun ≡ λ x → myFun x
  etaFun = refl

In particular, two lambda expressions with the same body up to renaming of the
argument(s) are considered equal.

::

  alpha : (λ x → x + 1) ≡ (λ y → y + 1)
  alpha = refl

Lambda expressions can take :ref:`implicit-arguments` and
:ref:`instance-arguments` by adding curly braces (resp. double curly braces)
around the argument.

::

  implicit-lambda = λ {A : Set} (x : A) → x

  instance-lambda = λ (A : Set) {{monoid-A : Monoid A}} → mempty

Arguments to lambda expressions can also be annotated with any :ref:`modality <modalities>`.

.. _pattern-lambda:

Pattern lambda
-----------------------

Anonymous pattern matching functions can be defined by a *pattern lambda* using
one of the two following syntaxes:

.. code-block:: agda

   \ { p11 .. p1n -> e1 ; … ; pm1 .. pmn -> em }

   \ where
     p11 .. p1n -> e1
     …
     pm1 .. pmn -> em

(where, as usual, ``\`` and ``->`` can be replaced by ``λ`` and ``→``).
Note that the ``where`` keyword introduces an *indented* block of clauses;
if there is only one clause then it may be used inline.

Examples of pattern lambdas:

::

  and : Bool → Bool → Bool
  and = λ { true x → x ; false _ → false }

  xor : Bool → Bool → Bool
  xor = λ { true  true  → false
          ; false false → false
          ; _     _     → true
          }

  eq : Bool → Bool → Bool
  eq = λ where
    true  true  → true
    false false → true
    _ _ → false

  myFst : {A : Set} {B : A → Set} → Σ A B → A
  myFst = λ { (a , b) → a }

  mySnd : {A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
  mySnd = λ { (a , b) → b }

  swap : {A B : Set} → A × B → B × A
  swap = λ where (a , b) → (b , a)

Pattern lambdas can also use :ref:`copatterns` by using projections in
:ref:`postfix notation <record-types>`.

::

  swap' : {A B : Set} → A × B → B × A
  swap' = λ where
    (a , b) .fst → b
    (a , b) .snd → a

It is not allowed to use ``where`` and ``with`` constructions in pattern lambdas.

Regular pattern lambdas are treated as non-erased function definitions (see
::ref:`runtime-irrelevance`). One can make a pattern lambda erased by writing
``@0`` or ``@erased`` before the lambda:

::

  @0 _ : @0 Set → Set
  _ = λ @0 { A → A }

  @0 _ : @0 Set → Set
  _ = λ @erased where
    A → A

Internal representation of pattern lambdas
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Internally pattern lambdas are translated into a function definition of the following form:

.. code-block:: agda

   extlam p11 .. p1n = e1
   …
   extlam pm1 .. pmn = em

where `extlam` is a fresh name. In other words, pattern lambdas are
*generative*. In particular, two pattern lambdas with the same body are not
considered equal by Agda (in contrast to regular lambda expressions).

..
  ::

  no-fun-ext : Set₀
  no-fun-ext =

::

    (λ { true → true ; false → false }) ==
    (λ { true → true ; false → false })

..
  ::
    where
      _==_ = _≡_ {A = Bool → Bool}

This type is equivalent to ``extlam1 ≡ extlam2`` for some distinct fresh names
``extlam1`` and ``extlam2``, hence cannot be proven with ``refl``.

.. _absurd-lambda:

Absurd lambda
--------------

An *absurd lambda* is a lambda expression that uses an
:ref:`absurd pattern <absurd-patterns>` ``()``.

::

  absurd-lambda : 0 ≡ 1 → ⊥
  absurd-lambda = λ ()

Unlike general pattern lambdas, absurd lambdas do not require curly braces or
the ``where`` keyword, although using them is still allowed.

::

  absurd-lambda-curly : 0 ≡ 1 → ⊥
  absurd-lambda-curly = λ { () }

  absurd-lambda-where : 0 ≡ 1 → ⊥
  absurd-lambda-where = λ where ()

It is also allowed to have regular arguments before or after the absurd pattern.

::

  absurd-lambda-list : {A : Set} (x : A) (xs : List A) → x ∷ xs ≡ [] → ⊥
  absurd-lambda-list = λ x xs ()
