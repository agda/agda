module _ where

module M where

open M using () renaming () hiding ()

-- empty lists should not be errors here
