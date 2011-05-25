module Agda.TypeChecking.Pretty where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.Utils.Pretty (Doc)
import qualified Agda.Utils.Pretty as P

text                  :: MonadTCM tcm => String             -> tcm Doc
sep, fsep, hsep, vcat :: MonadTCM tcm => [tcm Doc]          -> tcm Doc
($$), (<>), (<+>)     :: MonadTCM tcm => tcm Doc -> tcm Doc -> tcm Doc

class PrettyTCM a where
    prettyTCM :: MonadTCM tcm => a -> tcm Doc

instance PrettyTCM a => PrettyTCM (Closure a) where
instance PrettyTCM a => PrettyTCM [a] where

instance PrettyTCM Name where
instance PrettyTCM QName where
instance PrettyTCM Term where
instance PrettyTCM Type where
instance PrettyTCM Sort where
instance PrettyTCM DisplayTerm where
