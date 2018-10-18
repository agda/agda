-- Andreas, 2018-10-18, issue #3285, reported by ice1000
-- Testcase by Frederik NF

f : Set → Set
f x = x

syntax f a = a

-- WAS: internal error
--
-- Now: parse error: Malformed syntax declaration
