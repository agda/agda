module Agda.TypeChecking.Pretty where

import Data.String (IsString)
import Data.Semigroup (Semigroup)

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.MetaVars (MonadInteractionPoints)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Pure (PureTCM)

import Agda.Utils.Null (Null)
import Agda.Utils.Pretty (Doc)
import qualified Agda.Utils.Pretty as P


text                  :: Applicative m => String -> m Doc
sep, fsep, hsep, vcat :: (Applicative m, Foldable t) => t (m Doc) -> m Doc
hang                  :: Applicative m => m Doc -> Int -> m Doc -> m Doc
($$), (<+>), (<?>)    :: Applicative m => m Doc -> m Doc -> m Doc
nest                  :: Functor m => Int -> m Doc -> m Doc
pretty                :: (Applicative m, P.Pretty a) => a -> m Doc
prettyList_           :: (Applicative m, Semigroup (m Doc), Foldable t) => t (m Doc) -> m Doc
pwords                :: Applicative m => String -> [m Doc]

-- The definition of MonadAbsToCon is inlined so that the module
-- Agda.Syntax.Translation.AbstractToConcrete does not need to be
-- imported.
type MonadPretty m =
  ( MonadFresh NameId m
  , MonadInteractionPoints m
  , MonadStConcreteNames m
  , HasOptions m
  , PureTCM m
  , IsString (m Doc)
  , Null (m Doc)
  , Semigroup (m Doc)
  )

-- This instance is to satify the constraints of superclass MonadPretty:
-- This instance is more specific than a generic instance
-- @Semigroup a => Semigroup (TCM a)@.
instance {-# OVERLAPPING #-} Semigroup (TCM Doc)

class PrettyTCM a where
  prettyTCM :: MonadPretty m => a -> m Doc

newtype PrettyContext = PrettyContext Context

instance PrettyTCM a => PrettyTCM (Closure a)
instance PrettyTCM a => PrettyTCM [a]

instance PrettyTCM Name
instance PrettyTCM QName
instance PrettyTCM NamedMeta
instance PrettyTCM Term
instance PrettyTCM Elim
instance PrettyTCM Type
instance PrettyTCM Sort
instance PrettyTCM DisplayTerm
instance PrettyTCM DBPatVar
instance PrettyTCM PrettyContext
