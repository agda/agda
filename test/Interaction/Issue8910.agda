-- Andreas, 2026-11-4, issue #8910
-- Bug: Interactive highlighting clears the highlighting of the `import`
-- keyword in `open` statements with module applications.
-- The reproducer was constructed in dialogue with Codex/GPT-6.1-Sol.

module Issue8910 (A : Set) where

open import Issue8910.M A
