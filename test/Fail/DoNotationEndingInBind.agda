-- Andreas, 2024-08-31
-- Trigger error related to 'do' desugaring

postulate
  _>>=_ : Set → Set → Set

f = do x ← Set

-- Expected error:
-- The last statement in a 'do' block must be an expression or an absurd match.
