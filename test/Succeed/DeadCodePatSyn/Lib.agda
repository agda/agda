
module DeadCodePatSyn.Lib where

private
  data Hidden : Set where
    hidden : Hidden

pattern not-hidden = hidden
