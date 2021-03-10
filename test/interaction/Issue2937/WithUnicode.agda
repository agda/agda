module Issue2937.WithUnicode where

foo : _ → _ → Set
foo bar x =  λ x → foo (bar x {!!}) x
