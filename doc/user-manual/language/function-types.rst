.. _function-types:

**************
Function Types
**************

Function types are written ``(x : A) → B``, or in the case of non-dependent functions simply ``A → B``. For instance, the type of the addition function for natural numbers is::

 Nat → Nat → Nat

and the type of the addition function for vectors is:::

 (A : Set) → (n : Nat) → (u : Vec A n) → (v : Vec A n) → Vec A n

where ``Set`` is the type of sets and ``Vec A n`` is the type of vectors with ``n`` elements of type ``A``. Arrows between consecutive hypotheses of the form ``(x : A)`` may also be omitted, and ``(x : A) (y : A)`` may be shortened to ``(x y : A)``:::

 (A : Set) (n : Nat)(u v : Vec A n) → Vec A n

Functions are constructed by lambda abstractions, which can be either typed or untyped. For instance, both expressions below have type ``(A : Set) → A → A`` (the second expression checks against other types as well):::

 \ (A : Set)(x : A) → x
 \ A x → x

The application of a function ``f : (x : A) → B`` to an argument ``a : A`` is written ``f a`` and the type of this is ``B[x := a]``.

Notational conventions
----------------------

Function types:
::

 (x : A)(y : B) → C    is the same as (x : A) → (y : B) → C
 (x y : A) → C         is the same as (x : A)(y : A) → C
 forall (x : A) → C    is the same as (x : A) → C
 forall x → C          is the same as (x : _) → C
 forall x y → C        is the same as forall x → forall y → C

You can also use the Unicode symbol ``∀`` (type “\all” in the Emacs Agda mode) instead of forall.

Functional abstraction:::

 \x y → e is the same as \x → (\y → e)

Functional application:::

 f a b is the same as (f a) b.

