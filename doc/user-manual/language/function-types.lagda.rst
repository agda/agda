..
  ::
  {-# OPTIONS --allow-unsolved-metas --rewriting --sized-types #-}
  module language.function-types where

  open import language.built-ins

  data Vec (A : Set) : Nat → Set where
    nil : {n : Nat} → Vec A n
    cons : {n : Nat} (a : A) (as : Vec A n) → Vec A (suc n)

  _is-the-same-as_ = _≡_

.. _function-types:

**************
Function Types
**************

Function types are written ``(x : A) → B``, or in the case of non-dependent functions simply ``A → B``. For instance, the type of the addition function for natural numbers is:

..
  ::
  example-hidden₁ : Set
  example-hidden₁ =

::

    Nat → Nat → Nat

and the type of the addition function for vectors is:

..
  ::
  example-hidden₂ : Set₁
  example-hidden₂ =

::

    (A : Set) → (n : Nat) → (u : Vec A n) → (v : Vec A n) → Vec A n

where ``Set`` is the type of sets and ``Vec A n`` is the type of vectors with ``n`` elements of type ``A``. Arrows between consecutive hypotheses of the form ``(x : A)`` may also be omitted, and ``(x : A) (y : A)`` may be shortened to ``(x y : A)``:

..
  ::
  example-hidden₃ : Set₁
  example-hidden₃ =

::

    (A : Set) (n : Nat)(u v : Vec A n) → Vec A n

Functions are constructed by lambda abstractions, which can be either typed or untyped. For instance, both expressions below have type ``(A : Set) → A → A`` (the second expression checks against other types as well):

..
  ::
  example₁ example₂ : (A : Set) (x : A) → A

::


  example₁ = \ (A : Set)(x : A) → x
  example₂ = \ A x → x

You can also use the Unicode symbol ``λ`` (type “\\lambda” or “\\Gl” in the Emacs Agda mode) instead of ``\`` (type “\\\\” in the Emacs Agda mode).

The application of a function ``f : (x : A) → B`` to an argument ``a : A`` is written ``f a`` and the type of this is ``B[x := a]``.

.. _notational-conventions:

Notational conventions
----------------------

Function types:

..
  ::
  module hidden₁ (A B C : Set) where

::

    prop₁ : ((x : A) (y : B) → C) is-the-same-as   ((x : A) → (y : B) → C)
    prop₂ : ((x y : A) → C)       is-the-same-as   ((x : A)(y : A) → C)
    prop₃ : (forall (x : A) → C)  is-the-same-as   ((x : A) → C)
    prop₄ : (forall x → C)        is-the-same-as   ((x : _) → C)
    prop₅ : (forall x y → C)      is-the-same-as   (forall x → forall y → C)

..
  ::
    prop₁ = refl
    prop₂ = refl
    prop₃ = refl
    prop₄ = refl
    prop₅ = refl

You can also use the Unicode symbol ``∀`` (type “\\all” in the Emacs Agda mode) instead of ``forall``.

Functional abstraction:

..
  ::
  prop-hidden₁ : (A : Set) (e : A) →

::

    (\x y → e)                    is-the-same-as   (\x → (\y → e))

..
  ::
  prop-hidden₁ _ _ = refl


Functional application:

..
  ::
  prop-hidden₅ : (A B C : Set) (f : A → B → C) (a : A) (b : B) →

::

    (f a b)                       is-the-same-as    ((f a) b)

..
  ::
  prop-hidden₅ _ _ _ _ _ _ = refl
