-- Szumi, 2025-06-21, issue #7955.
-- '..' followed by variable used to parse but caused an internal error.

f = ..x

-- Expected error: [SyntaxError]
-- Syntax error: unexpected '..'
-- when scope checking ..x
