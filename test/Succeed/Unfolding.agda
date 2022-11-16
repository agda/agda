module Unfolding where

open import Agda.Builtin.Nat

{-
Abstract blocks can now have an 'unfolding' clause, expressing a subset
of the abstract definitions in scope that are treated transparently
within scope of that block. The user experience is as follows: In an
"abstract unfolding (foo)" block, Agda will unfold the definition of
foo, of any abstract definitions foo unfolds, and of any other
definitions in the same abstract blocks as one of those.

I will now feel free to exposit on the internal implementation:

Each abstract block is internally associated with a unique identifier
(essentially, an integer), and this identifier is associated with a
*set* of names that should be treated transparently. Initially, the set
is empty for every abstract block. We then scope-check the definitions
which belong to this abstract block: Each scope-checked definition is
added to the corresponding set. For example,
-}

module A where
  abstract -- Let's call this abstract block 1.
    foo : Set₁
    foo = Set
  -- The definition 'foo' belongs to abstract block 1, so after
  -- scope-checking 'foo', the internal mapping of ids→sets looks like
  --  1 → {foo}
  -- and since block 1 has no 'unfolding' clause, this is its final set
  -- of names. We also maintain a mapping
  --   foo → 1
  -- of names to abstract blocks.

{-
When scope-checking an 'unfolding (foo)' declaration, we add the name
'foo' to the set of transparent definitions, as well as any name which
the abstract block associated with foo (1) can unfold.
-}

module B where
  open A
  abstract unfolding (foo) where -- Block 2.
    bar : foo
    bar = Nat
  -- Here, we have a mapping 2 → {bar}, since bar belongs to 2. But
  -- block 2 may also unfold foo, so we take a union and update
  --   2 → {foo} ∪ {bar} = {foo, bar}
  -- This implements a transitive closure of the transparent
  -- definitions.

module C where
  open A
  open B
  abstract unfolding (bar) where -- Block 3.
  -- We note that the calculation of unfolding sets happens before
  -- type-checking, so that both in block 2 and here, we already know
  -- ahead-of-time what can be unfolded. For block 3, we have
  --  3 → {ty, quux}
  -- and 3 unfolds bar. We know that bar belongs to the abstract block
  -- 2, and we have a mapping
  --  2 → {foo, bar}
  -- so that 3 has the final set
  --  3 → {ty, quux, foo, bar}
    ty : Set
    ty = bar

    quux : ty
    quux = zero
