{-# LANGUAGE TypeFamilies #-}

-- | Extract used definitions from terms.

module Agda.Syntax.Internal.Defs where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold

import Agda.Syntax.Common
import Agda.Syntax.Internal

-- | @getDefs' lookup emb a@ extracts all used definitions
--   (functions, data/record types) from @a@, embedded into a monoid via @emb@.
--   Instantiations of meta variables are obtained via @lookup@.
--
--   Typical monoid instances would be @[QName]@ or @Set QName@.
--   Note that @emb@ can also choose to discard a used definition
--   by mapping to the unit of the monoid.
getDefs' :: (GetDefs a, Monoid b) => (MetaId -> Maybe Term) -> (QName -> b) -> a -> b
getDefs' lookup emb = execWriter . (`runReaderT` GetDefsEnv lookup emb) . getDefs

-- | Inputs to and outputs of @getDefs'@ are organized as a monad.
type GetDefsM b = ReaderT (GetDefsEnv b) (Writer b)

data GetDefsEnv b = GetDefsEnv
  { lookupMeta :: MetaId -> Maybe Term
  , embDef     :: QName -> b
  }

-- | What it takes to get the used definitions.
class Monad m => MonadGetDefs m where
  doDef  :: QName -> m ()
  doMeta :: MetaId -> m ()

instance Monoid b => MonadGetDefs (GetDefsM b) where
  doDef  d = tell . ($ d) =<< asks embDef
  doMeta x = getDefs . ($ x) =<< asks lookupMeta

-- | Getting the used definitions.
--
-- Note: in contrast to 'Agda.Syntax.Internal.Generic.foldTerm'
-- @getDefs@ also collects from sorts in terms.
-- Thus, this is not an instance of @foldTerm@.

class GetDefs a where
  getDefs :: MonadGetDefs m => a -> m ()

  default getDefs :: (MonadGetDefs m, Foldable f, GetDefs b, f b ~ a) => a -> m ()
  getDefs = Fold.mapM_ getDefs

instance GetDefs Clause where
  getDefs = getDefs . clauseBody

instance GetDefs Term where
  getDefs v = case v of
    Def d vs   -> doDef d >> getDefs vs
    Con _ _ vs -> getDefs vs
    Lit l      -> return ()
    Var i vs   -> getDefs vs
    Lam _ v    -> getDefs v
    Pi a b     -> getDefs a >> getDefs b
    Sort s     -> getDefs s
    Level l    -> getDefs l
    MetaV x vs -> getDefs x >> getDefs vs
    DontCare v -> getDefs v
    Dummy{}    -> return ()

instance GetDefs MetaId where
  getDefs x = doMeta x

instance GetDefs Type where
  getDefs (El s t) = getDefs s >> getDefs t

instance GetDefs Sort where
  getDefs s = case s of
    Type l    -> getDefs l
    Prop l    -> getDefs l
    Inf       -> return ()
    SizeUniv  -> return ()
    PiSort a s  -> getDefs a >> getDefs s
    UnivSort s  -> getDefs s
    MetaS x es  -> getDefs x >> getDefs es
    DefS d es   -> doDef d >> getDefs es
    DummyS{}    -> return ()

instance GetDefs Level where
  getDefs (Max ls) = getDefs ls

instance GetDefs PlusLevel where
  getDefs ClosedLevel{} = return ()
  getDefs (Plus _ l)    = getDefs l

instance GetDefs LevelAtom where
  getDefs a = case a of
    MetaLevel x vs   -> getDefs x >> getDefs vs
    BlockedLevel _ v -> getDefs v
    NeutralLevel _ v -> getDefs v
    UnreducedLevel v -> getDefs v

-- collection instances

instance GetDefs a => GetDefs (Maybe a) where
instance GetDefs a => GetDefs [a]       where
instance GetDefs a => GetDefs (Elim' a) where
instance GetDefs a => GetDefs (Arg a)   where
instance GetDefs a => GetDefs (Dom a)   where
instance GetDefs a => GetDefs (Abs a)   where

instance (GetDefs a, GetDefs b) => GetDefs (a,b) where
  getDefs (a,b) = getDefs a >> getDefs b
