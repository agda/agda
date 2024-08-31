-- Andreas, 2024-08-31
-- Trigger error related to 'do' desugaring

f = do x ← Set; x

-- Expected error:
-- _>>=_ needs to be in scope to desugar 'do' block
