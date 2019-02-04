{-# LANGUAGE FlexibleInstances #-}

module Agda.TypeChecking.Pretty where

-- import Agda.Syntax.Common
import Agda.Syntax.Internal
-- import Agda.Syntax.Literal

import Agda.TypeChecking.Monad.Base
import Agda.Utils.Pretty (Doc)
-- import qualified Agda.Utils.Pretty as P

text                  :: Monad m => String -> m Doc
sep, fsep, hsep, vcat :: Monad m => [m Doc] -> m Doc
($$), (<>), (<+>)     :: Applicative m => m Doc -> m Doc -> m Doc

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
