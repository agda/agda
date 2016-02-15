{-# OPTIONS -v interaction.case:65 #-}

data Bool : Set where
  true false : Bool

test : Bool → Bool
test x = {!x!}
