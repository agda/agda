<!-- Test for issue #7971: https://github.com/agda/agda/issues/7971
     Date: 2025-12-01

     This test demonstrates that when --literate-md-only-agda-blocks is enabled,
     necessary Agda code placed in unmarked code blocks is NOT picked up,
     causing subsequent Agda code blocks to fail.

     Note: The option is passed via .flags file because it affects parsing,
     which happens before pragma options are applied.

     Expected behavior: The module should fail to type-check because the data
     type definition in the unmarked block is not processed.
-->

# Failing Test for Literate Markdown Only Agda Blocks

This file demonstrates what happens when necessary Agda code is placed in
an unmarked code block.

```agda
module Issue7971LiterateMdOnlyAgdaBlocksFail where
```

## Missing Definition

The following data type is defined in an UNMARKED code block, so it will
NOT be type-checked when `--literate-md-only-agda-blocks` is enabled:

```
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
```

## This Will Fail

The following code tries to use `Nat`, but since the definition above was
in an unmarked block, `Nat` is not in scope:

```agda
-- This should fail because Nat is not defined
double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))
```
