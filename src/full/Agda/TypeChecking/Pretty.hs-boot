{-# LANGUAGE FlexibleInstances #-}

module Agda.TypeChecking.Pretty where

-- import Agda.Syntax.Common
import Agda.Syntax.Internal
-- import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.Utils.Pretty (Doc)
-- import qualified Agda.Utils.Pretty as P

text                  :: String             -> TCM Doc
sep, fsep, hsep, vcat :: [TCM Doc]          -> TCM Doc
($$), (<>), (<+>)     :: TCM Doc -> TCM Doc -> TCM Doc

class PrettyTCM a where
    prettyTCM :: a -> TCM Doc

instance PrettyTCM a => PrettyTCM (Closure a)
instance PrettyTCM a => PrettyTCM [a]

instance PrettyTCM Name
instance PrettyTCM QName
instance PrettyTCM Term
instance PrettyTCM Elim
instance PrettyTCM Type
instance PrettyTCM Sort
instance PrettyTCM DisplayTerm
instance PrettyTCM DBPatVar
