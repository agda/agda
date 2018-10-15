
module _ where

module Inner where

  private
    variable A : Set

open Inner

fail : A → A
fail x = x
