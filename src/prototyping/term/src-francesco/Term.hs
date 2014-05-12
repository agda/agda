{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
module Term
    ( module Term.Types
    , module Term.Monad
    -- , module Term.Pretty
    ) where

import Term.Types
import Term.Monad