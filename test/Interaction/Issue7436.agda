-- Andreas, 2024-09-02, regression #7436 in dead code removal.
-- Shrank original reproducer by mechvel.

{-# OPTIONS --no-main #-}

open import Issue7436.Import Set

-- WAS: Internal error (unbound identifier) during compilation,
-- only reliably reproduceable from the command line.

-- Should succeed.
