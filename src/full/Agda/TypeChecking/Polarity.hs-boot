{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Polarity where

import Agda.Syntax.Abstract.Name    ( QName )
import Agda.TypeChecking.Monad.Base ( Polarity, TCM )

computePolarity :: [QName] -> TCM ()
composePol      :: Polarity -> Polarity -> Polarity
