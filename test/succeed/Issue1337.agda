-- Andreas, 2014-11-01, reported by Andrea Vezzosi

-- Non-printable characters in line comments

-- Soft hyphen in comment creates lexical error:
-- ­ (SOFT HYPHEN \- 0xAD)

-- Or parse error:
-- A ­
