-- Patterns are parsed as expressions. That means that expressions can contain
-- pattern parts. That's of course not ok.
module NotAnExpression where

X = x @ y -- as pattern as an expression

