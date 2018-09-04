module AbsurdPatternRequiresNoRHS where

data   False : Set where
record True  : Set where

f : False -> True
f () = _

