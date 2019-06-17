..
  ::
  module language.syntactic-sugar where

  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality
  open import Agda.Builtin.String

  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  concatMap : {A B : Set} → (A → List B) → List A → List B
  concatMap f [] = []
  concatMap f (x ∷ xs) = f x ++ concatMap f xs

  data Either (A B : Set) : Set where
    left : A → Either A B
    right : B → Either A B

  record Applicative (F : Set → Set) : Set₁ where
    field
      pure  : ∀ {A} → A → F A
      _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  open Applicative {{...}}

  record Monad (M : Set → Set) : Set₁ where
    field
      _>>=_ : ∀ {A B} → M A → (A → M B) → M B
      overlap {{super}} : Applicative M
  open Monad {{...}}

  instance
    ApplicativeList : Applicative List
    pure  {{ApplicativeList}}       = _∷ []
    _<*>_ {{ApplicativeList}} fs xs = concatMap (λ f → concatMap (λ x → f x ∷ []) xs) fs

    MonadList : Monad List
    _>>=_ {{MonadList}} xs f = concatMap f xs

    ApplicativeEither : ∀ {Err} → Applicative (Either Err)
    pure  {{ApplicativeEither}} = right
    _<*>_ {{ApplicativeEither}} (left err) _ = left err
    _<*>_ {{ApplicativeEither}} (right f) (left err) = left err
    _<*>_ {{ApplicativeEither}} (right f) (right x)  = right (f x)

    MonadEither : ∀ {Err} → Monad (Either Err)
    _>>=_ {{MonadEither}} (left  e) f = left e
    _>>=_ {{MonadEither}} (right x) f = f x

.. _syntactic-sugar:

***************
Syntactic Sugar
***************

.. contents::
   :depth: 2
   :local:

.. _do-notation:

Do-notation
===========

A *do-block* consists of the :ref:`layout keyword <lexical-structure-layout>`
``do`` followed by a sequence of *do-statements*, where

.. code-block:: text

   do-stmt    ::= pat ← expr [where lam-clauses]
                | let decls
                | expr
   lam-clause ::= pat → expr

The ``where`` clause of a bind is used to handle the cases not matched by the pattern
left of the arrow. See :ref:`details below <do-desugaring>`.

.. note::
  Arrows can use either unicode (``←``/``→``) or ASCII (``<-``/``->``) variants.

For example::

  filter : {A : Set} → (A → Bool) → List A → List A
  filter p xs = do
    x    ← xs
    true ← p x ∷ []
      where false → []
    x ∷ []

Do-notation is desugared before scope checking and is translated into calls to ``_>>=_`` and ``_>>_``, whatever those happen to be bound in the context of the do-block. This means that do-blocks are not tied to any particular notion of monad. In fact if there are no monadic statements in the do block it can be used as sugar for a ``let``::

  pure-do : Nat → Nat
  pure-do n = do
    let p2 m = m * m
        p4 m = p2 (p2 m)
    p4 n

  check-pure-do : pure-do 5 ≡ 625
  check-pure-do = refl

.. _do-desugaring:

Desugaring
----------

+---------------+----------------------+----------------------+
| Statement     | Sugar                | Desugars to          |
+===============+======================+======================+
| Simple bind   | ::                   | ::                   |
|               |                      |                      |
|               |   do x ← m           |     m >>= λ x →      |
|               |      m'              |     m'               |
+---------------+----------------------+----------------------+
| Pattern bind  | ::                   | ::                   |
|               |                      |                      |
|               |   do p ← m           |   m >>= λ where      |
|               |        where pᵢ → mᵢ |            p  → m'   |
|               |      m'              |            pᵢ → mᵢ   |
+---------------+----------------------+----------------------+
| Non-binding   | ::                   | ::                   |
| statement     |                      |                      |
|               |   do m               |     m >>             |
|               |      m'              |     m'               |
+---------------+----------------------+----------------------+
| Let           | ::                   | ::                   |
|               |                      |                      |
|               |   do let ds          |     let ds in        |
|               |      m'              |     m'               |
+---------------+----------------------+----------------------+

If the pattern in the bind is exhaustive, the where-clause can be omitted.

Example
-------

Do-notation becomes quite powerful together with pattern matching on indexed data. As an example,
let us write a correct-by-construction type checker for simply typed λ-calculus.

First we define the raw terms, using de Bruijn indices for variables and explicit type
annotations on the lambda::

  infixr 6 _=>_
  data Type : Set where
    nat  : Type
    _=>_ : (A B : Type) → Type

  data Raw : Set where
    var : (x : Nat) → Raw
    lit : (n : Nat) → Raw
    suc : Raw
    app : (s t : Raw) → Raw
    lam : (A : Type) (t : Raw) → Raw

Next up, well-typed terms::

  Context = List Type

  -- A proof of x ∈ xs is the index into xs where x is located.
  infix 2 _∈_
  data _∈_ {A : Set} (x : A) : List A → Set where
    zero : ∀ {xs} → x ∈ x ∷ xs
    suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

  data Term (Γ : Context) : Type → Set where
    var : ∀ {A} (x : A ∈ Γ) → Term Γ A
    lit : (n : Nat) → Term Γ nat
    suc : Term Γ (nat => nat)
    app : ∀ {A B} (s : Term Γ (A => B)) (t : Term Γ A) → Term Γ B
    lam : ∀ A {B} (t : Term (A ∷ Γ) B) → Term Γ (A => B)

Given a well-typed term we can mechaincally erase all the type
information (except the annotation on the lambda) to get the
corresponding raw term::

  rawIndex : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
  rawIndex zero    = zero
  rawIndex (suc i) = suc (rawIndex i)

  eraseTypes : ∀ {Γ A} → Term Γ A → Raw
  eraseTypes (var x)   = var (rawIndex x)
  eraseTypes (lit n)   = lit n
  eraseTypes suc       = suc
  eraseTypes (app s t) = app (eraseTypes s) (eraseTypes t)
  eraseTypes (lam A t) = lam A (eraseTypes t)

Now we're ready to write the type checker. The goal is to have a function that takes a
raw term and either fails with a type error, or returns a well-typed term that erases to
the raw term it started with. First, lets define the return type. It's parameterised by
a context and the raw term to be checked::

  data WellTyped Γ e : Set where
    ok : (A : Type) (t : Term Γ A) → eraseTypes t ≡ e → WellTyped Γ e

We're going to need a corresponding type for variables::

  data InScope Γ n : Set where
    ok : (A : Type) (i : A ∈ Γ) → rawIndex i ≡ n → InScope Γ n

Lets also have a type synonym for the case when the erasure proof is ``refl``::

  infix 2 _ofType_
  pattern _ofType_ x A = ok A x refl

Since this is a do-notation example we had better have a monad. Lets use the either
monad with string errors::

  TC : Set → Set
  TC A = Either String A

  typeError : ∀ {A} → String → TC A
  typeError = left

For the monad operations, we are using :ref:`instance arguments <instance-arguments>`
to infer which monad is being used.

We are going to need to compare types for equality. This is our first opportunity to take
advantage of pattern matching binds::

  _=?=_ : (A B : Type) → TC (A ≡ B)
  nat      =?= nat      = pure refl
  nat      =?= (_ => _) = typeError "type mismatch: nat ‌≠ _ => _"
  (_ => _) =?= nat      = typeError "type mismatch: _ => _ ≠ nat"
  (A => B) =?= (A₁ => B₁) = do
    refl ← A =?= A₁
    refl ← B =?= B₁
    pure refl

We will also need to look up variables in the context::

  lookupVar : ∀ Γ n → TC (InScope Γ n)
  lookupVar []      n       = typeError "variable out of scope"
  lookupVar (A ∷ Γ) zero    = pure (zero ofType A)
  lookupVar (A ∷ Γ) (suc n) = do
    i ofType B ← lookupVar Γ n
    pure (suc i ofType B)

Note how the proof obligation that the well-typed deBruijn index erases to
the given raw index is taken care of completely under the hood (in this case
by the ``refl`` pattern in the ``ofType`` synonym).

Finally we are ready to implement the actual type checker::

  infer : ∀ Γ e → TC (WellTyped Γ e)
  infer Γ (var x)    = do
    i ofType A ← lookupVar Γ x
    pure (var i ofType A)
  infer Γ (lit n)    = pure (lit n ofType nat)
  infer Γ suc        = pure (suc ofType nat => nat)
  infer Γ (app e e₁) = do
    s ofType A => B ← infer Γ e
      where _ ofType nat → typeError "numbers cannot be applied to arguments"
    t ofType A₁     ← infer Γ e₁
    refl            ← A =?= A₁
    pure (app s t ofType B)
  infer Γ (lam A e)  = do
    t ofType B ← infer (A ∷ Γ) e
    pure (lam A t ofType A => B)

In the ``app`` case we use a where-clause to handle the error case when the
function to be applied is well-typed, but does not have a function type.

.. _idiom-brackets:

Idiom brackets
==============

Idiom brackets is a notation used to make it more convenient to work with applicative
functors, i.e. functors ``F`` equipped with two operations

.. code-block:: agda

  pure  : ∀ {A} → A → F A
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B

As do-notation, idiom brackets desugar before scope checking, so whatever the names ``pure``
and ``_<*>_`` are bound to gets used when desugaring the idiom brackets.

The syntax for idiom brackets is

.. code-block:: agda

  (| e a₁ .. aₙ |)

or using unicode lens brackets ``⦇`` (U+2987) and  ``⦈`` (U+2988):

.. code-block:: agda

  ⦇ e a₁ .. aₙ ⦈

This expands to (assuming left associative ``_<*>_``)

.. code-block:: agda

  pure e <*> a₁ <*> .. <*> aₙ

Idiom brackets work well with operators, for instance

.. code-block:: agda

  (| if a then b else c |)

desugars to

.. code-block:: agda

  pure if_then_else_ <*> a <*> b <*> c

Idiom brackets also support none or multiple applications. If the applicative
functor has an additional binary operation

.. code-block:: agda

  _<|>_ : ∀ {A B} → F A → F A → F A

then idiom brackets support multiple applications separated by a vertical bar ``|``, i.e.

.. code-block:: agda

  (| e₁ a₁ .. aₙ | e₂ a₁ .. aₘ | .. | eₖ a₁ .. aₗ |)

which expands to (assuming right associative ``_<|>_``)

.. code-block:: agda

  (pure e₁ <*> a₁ <*> .. <*> aₙ) <|> ((pure e₂ <*> a₁ <*> .. <*> aₘ) <|> (pure eₖ <*> a₁ <*> .. <*> aₗ))

Idiom brackets without any application ``(|)`` or ``⦇⦈`` expend to ``empty`` if

.. code-block:: agda

  empty :  ∀ {A} → F A

is in scope. An applicative functor with ``empty`` and ``_<|>_`` is typically
called ``Alternative``.

Note that ``pure``, ``_<*>_``, and ``_<|>_`` need not be in scope to use ``(|)``.

Limitations:

- Binding syntax and operator sections cannot appear immediately inside
  idiom brackets.

- The top-level application inside idiom brackets cannot include
  implicit applications, so

  .. code-block:: agda

     (| foo {x = e} a b |)

  is illegal. In case the ``e`` is pure you can write

  .. code-block:: agda

     (| (foo {x = e}) a b |)

  which desugars to

  .. code-block:: agda

     pure (foo {x = e}) <*> a <*> b
