
module Agda.TypeChecking.Pretty where

import Data.String (IsString)
import Data.Semigroup (Semigroup)

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal
-- import Agda.Syntax.Literal
import Agda.Syntax.Position (Range)

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Builtin
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context (MonadAddContext)
import Agda.TypeChecking.Monad.Debug (MonadDebug)
import {-# SOURCE #-} Agda.TypeChecking.Monad.MetaVars (MonadInteractionPoints)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.Utils.Null (Null)
import Agda.Utils.Pretty (Doc)
-- import qualified Agda.Utils.Pretty as P

text                  :: Monad m => String -> m Doc
sep, fsep, hsep, vcat :: Monad m => [m Doc] -> m Doc
($$), (<+>)           :: Applicative m => m Doc -> m Doc -> m Doc

-- Inlining definitions of MonadReify and MonadAbsToCon to avoid
-- having to import them
type MonadPretty m =
  ( ( MonadReduce m
    , MonadAddContext m
    , MonadInteractionPoints m
    , MonadFresh NameId m
    , HasConstInfo m
    , HasOptions m
    , HasBuiltins m
    , MonadDebug m
    )
  , ( MonadTCEnv m
    , ReadTCState m
    , MonadStConcreteNames m
    , HasOptions m
    , HasBuiltins m
    , MonadDebug m
    )
  , IsString (m Doc)
  , Null (m Doc)
  , Semigroup (m Doc)
  )

class PrettyTCM a where
  prettyTCM :: MonadPretty m => a -> m Doc

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
