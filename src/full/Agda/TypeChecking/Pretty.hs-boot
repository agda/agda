module Agda.TypeChecking.Pretty where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.Utils.Pretty (Doc)
import qualified Agda.Utils.Pretty as P

text                  :: String             -> TCM Doc
sep, fsep, hsep, vcat :: [TCM Doc]          -> TCM Doc
($$), (<>), (<+>)     :: TCM Doc -> TCM Doc -> TCM Doc

class PrettyTCM a where
    prettyTCM :: a -> TCM Doc

instance PrettyTCM a => PrettyTCM (Closure a) where
instance PrettyTCM a => PrettyTCM [a] where

instance PrettyTCM Name where
instance PrettyTCM QName where
instance PrettyTCM Term where
instance PrettyTCM Type where
instance PrettyTCM Sort where
instance PrettyTCM DisplayTerm where
