--2010-09-28

module AbsurdIrrelevance where

data Empty : Set where

absurd : {A : Set} -> .Empty -> A
absurd ()
 