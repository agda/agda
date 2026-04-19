-- Andreas, 2026-04-19, issue #8521, reported by flipette
-- Pushing a dot under a parenthesized pattern
-- should rule it out as projection pattern.

record ⊤ : Set where

record S : Set where
  field f : ⊤

module M where
  open S

  hidden : .{_ : S → ⊤} → Set
  hidden .{f} = S

  -- This is parsed as {.f} as the dot is pushed under the braces.
  -- However, this should never be interpreted as projection pattern.
  -- WAS: internal error.

  paren : .(_ : S → ⊤) → Set
  paren .(f) = S

open S {{...}}

inst : .{{_ : {{S}} → ⊤}} → Set
inst .{{f}} = S
