{-# OPTIONS --no-unicode #-}

module Issue2937.NoUnicode where

foo : _ -> _ -> Set
foo bar x = \x -> foo (bar x {!!}) x
