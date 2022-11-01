NOTE: Put drafts of release notes here that might be included in some
future release.

Erasure
-------

* Added a hard compile-time mode (see
  [#4743](https://github.com/agda/agda/issues/4743)).

  When the hard compile-time mode is used all definitions are treated
  as erased. The hard compile-time mode is entered when an erased
  definition is checked, but not when (for instance) a type-signature
  is checked.

  Previously the following code was rejected:
  ```agda
  open import Agda.Builtin.Bool

  @0 f : @0 Bool → Bool
  f = λ where
    true  → false
    false → true
  ```
  Now this code is accepted. On the other hand, the following code
  which used to be accepted is now rejected, because the
  pattern-matching lambda is treated as erased:
  ```agda
  open import Agda.Builtin.Equality

  data Unit : Set where
    unit : Unit

  mutual

    f : Unit → Unit
    f = _

    @0 f≡ : f ≡ λ { unit → unit }
    f≡ = refl

* One can now mark data and record types as erased (see
  [#4743](https://github.com/agda/agda/issues/4743)).

  If a data type is marked as erased, then it can only be used in
  erased settings, and its constructors are erased. A data type is
  marked as erased by writing `@0` or `@erased` right after the `data`
  keyword of the data type's declaration:
  ```agda
  data @0 D₁ : Set where
    c : D₁

  data @0 D₂ : Set

  data D₂ where
    c : D₁ → D₂

  interleaved mutual

    data @0 D₃ : Set where

    data D₃ where
      c : D₃
  ```

  If a record type is marked as erased, then it can only be used in
  erased settings, its constructors and fields are erased, and
  definitions in the record module are erased. A record type is marked
  as erased by writing `@0` or `@erased` right after the `record`
  keyword of the record type's declaration:
  ```agda
  record @0 R₁ : Set where
    field
      x : D₁

  record @0 R₂ : Set

  record R₂ where
    field
      x : R₁
  ```

Pragmas and Options
-------------------

* The option `--termination-depth` is now obsolete.

  The default termination depth is now infinity instead of
  (previously) 1.  This means that setting `--termination-depth` might
  now make the termination checker *weaker* (instead of stronger).
  However, there is no guaranteed effect of setting
  `--termination-depth` any more.  The flag is only kept for debugging
  Agda.

  For example, the following code now passes the termination checker
  (needed higher `--termination-depth` before):

  ```agda
  f : Nat → Nat
  g : Nat → Nat

  f zero                = zero
  f (suc zero)          = zero
  f (suc (suc zero))    = zero
  f (suc (suc (suc n))) = g n     -- decrease by 3

  g n = f (suc (suc n))           -- increase by 2
  ```

  [See also Issue [#709](https://github.com/agda/agda/issues/709)]
