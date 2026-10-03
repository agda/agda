---
title: `UnusedImports` warnings concerning modules
author: Andreas Abel
date: 2025-12-08
---

```agda
{-# OPTIONS -WUnusedImports #-}

-- {-# OPTIONS -v warning.unusedImports:60 #-}

module _ where
```

# Unused module in `using` directive.

```agda
open import Agda.Builtin.Equality using (module _≡_)
```
This should warn about the unused `module _≡_` and highlight it.

# Unused module in `renaming` directive.
```agda
open import Agda.Builtin.Equality using () renaming (module _≡_ to Eq)
```
This should warn about the unused module `Eq` and highlight it.


# A module that just exports an unused module

```agda
module Parent where
  module Child where
   postulate A : Set

module Mod1 where
  open Parent
```
The `open` should be reported as redundant.

# A module that just exports an module used in qualification

```agda
module Mod2 where
  open Parent
  postulate x : Child.A
```
There should be no warning for this `open` statement

# Importing just a module but this one is used

```agda
import Agda.Builtin.Nat

Nat = Agda.Builtin.Nat.Nat

module Nat1 where
  open Agda.Builtin.Nat using (module Nat)  -- no warning
  open Nat -- no warning

  plus : (x y : Nat) → Nat
  plus zero y = y
  plus (suc x) y = suc (plus x y)
```
No warnings about unused imports expected here.

# Using a module in qualified names

```agda
module Nat2 where
  open Agda.Builtin.Nat using (module Nat)  -- no warning

  plus : (x y : Nat) → Nat
  plus Nat.zero y = y
  plus (Nat.suc x) y = Nat.suc (plus x y)
```
The imported module `Nat` is used qualified so not redundantly imported.

# Using a module brought into scope in another `open` statement

```agda
module Mod3 where
  open Parent  -- no warning, since Child is used below
  open Child   -- no warning, since A is used below

  postulate y : A
```

# Using a nested module in a qualified name

```agda
module Grand where
  module Father where
    module Son where
      postulate B : Set

module Mod4 where
  open Grand  -- no warning, since Father is used below
  postulate z : Father.Son.B
```

# Using a module in a module application

```agda
module Mod5 where
  open Parent  -- no warning, since Child is used below
  module C = Child
```

# Using a module in a `let open`

```agda
module Mod6 where
  open Parent  -- no warning, since Child is used below
  postulate B : Set
  b : Set
  b = let open Child in B
```
Since `A` is not used, the `let open Child` is redundant and should be reported.

# Using the module of a record type

```agda
module Rec where
  record R : Set₁ where
    field
      f : Set

module Mod7 where
  open Rec  -- no warning, since R is used below
  g : Rec.R → Set
  g r = R.f r
```

# Explicitly imported module of a data type is not used

```agda
module Bool1 where
  open import Agda.Builtin.Bool using (Bool; module Bool)
  t : Bool
  t = Agda.Builtin.Bool.true
```
Only the module `Bool` is unused and should be reported.

# The implicitly imported module of a data type is not reported

```agda
module Bool2 where
  open import Agda.Builtin.Bool using (Bool; true)
  t : Bool
  t = true
```
No warning: the module `Bool` comes along with the name `Bool`.

# Using a module qualified, while names are unused

```agda
module Bool3 where
  open import Agda.Builtin.Bool
  t : Agda.Builtin.Bool.Bool
  t = Bool.true
```
No warning, since module `Bool` is used.

# Ambiguous qualifier

```agda
module P1 where
  module X where
    postulate a : Set

module P2 where
  module X where
    postulate b : Set

module Mod8 where
  open P1  -- no warning, since X.a goes through P1.X
  open P2  -- redundant, since P2.X is not used
  postulate c : X.a
```
Only the opening of `P2` should be reported as redundant.

# The module of a record type copied by module application is not reported

```agda
module Mod9 where
  module Param (X : Set) where
    record R : Set where

  postulate X : Set
  open Param X using (R)

  r : R
  r = record{}
```
No warning: the module `R` comes along with the name `R`.
