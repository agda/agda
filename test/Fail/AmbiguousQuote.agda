
module AmbiguousQuote where

data A1 : Set where
  AC : A1

data A2 : Set where
  AC : A2

-- AC is ambiguous, could refer to the one coming from A1 or A2
test = quote AC
