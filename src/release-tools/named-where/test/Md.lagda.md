# Markdown literate test

A decoy in prose: `module Decoy where` should be ignored.

```agda
module Md where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

module Ordinary where
  ok : Nat
  ok = 0

f : Bool → Nat
f b with b
... | true  = 0
... | false = 1
  module W where
  q : Nat
  q = 1
```

A decoy in a non-Agda code block:

```haskell
module Decoy2 where
```
