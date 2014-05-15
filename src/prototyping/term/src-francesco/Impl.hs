module Impl
    ( -- * Base 'Term'
      Term
    , TermElim
    , Type
    , ClosedTerm
    , ClosedType
    , eliminate
    , absApply
    , absBody
    , absName
      -- * 'view' and 'unview'
    , TermView
    , view
    , unview
    , module Impl.Definition
    , module Impl.Monad
    ) where

import Impl.Term
import Impl.Definition
import Impl.Monad
