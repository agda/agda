module Impl
    ( -- * Base 'Term'
      Term
    , TermElim
    , Type
    , ClosedTerm
    , ClosedType
    , eliminate
      -- * 'view' and 'unview'
    , TermView
    , view
    , unview
    , module Impl.Telescope
    , module Impl.Definition
    , module Impl.Context
    , module Impl.Monad
    ) where

import Impl.Term
import Impl.Telescope
import Impl.Definition
import Impl.Context
import Impl.Monad
