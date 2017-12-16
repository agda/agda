-- Andreas, 2017-12-16, issue #2870
-- Nicer error for non-printable character in lexer.

postulate
  beforeHyphen­afterHyphen : Set

-- Expected something like:
-- Lexical error (unprintable character)
