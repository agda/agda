..
  ::
  module language.pattern-synonyms where

.. _pattern-synonyms:

****************
Pattern Synonyms
****************

A **pattern synonym** is a declaration that can be used on the left hand
side (when pattern matching) as well as the right hand side (in
expressions). For example::

    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ

    pattern z    = zero
    pattern ss x = suc (suc x)

    f : ℕ → ℕ
    f z       = z
    f (suc z) = ss z
    f (ss n)  = n

Pattern synonyms are implemented by substitution on the abstract
syntax, so definitions are scope-checked but *not type-checked*. They
are particularly useful for universe constructions.
