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
