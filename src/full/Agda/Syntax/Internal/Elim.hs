{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Internal.Elim where

import Control.DeepSeq

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Pretty () -- Pretty Arg instance
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name

import Agda.Utils.Pretty
import Agda.Utils.Empty
import Agda.Utils.Maybe
import Agda.Utils.Tuple

-- | Eliminations, subsuming applications and projections.
--
data Elim' a
  = Apply (Arg a)         -- ^ Application.
  | Proj ProjOrigin QName -- ^ Projection.  'QName' is name of a record projection.
  | IApply a a a -- ^ IApply x y r, x and y are the endpoints
  deriving (Show, Functor, Foldable, Traversable)

-- | This instance cheats on 'Proj', use with care.
--   'Proj's are always assumed to be 'UserWritten', since they have no 'ArgInfo'.
--   Same for IApply
instance LensOrigin (Elim' a) where
  getOrigin (Apply a)   = getOrigin a
  getOrigin Proj{}      = UserWritten
  getOrigin IApply{}    = UserWritten
  mapOrigin f (Apply a) = Apply $ mapOrigin f a
  mapOrigin f e@Proj{}  = e
  mapOrigin f e@IApply{} = e

-- | Drop 'Apply' constructor. (Safe)
isApplyElim :: Elim' a -> Maybe (Arg a)
isApplyElim (Apply u) = Just u
isApplyElim Proj{}    = Nothing
isApplyElim (IApply _ _ r) = Just (defaultArg r)

isApplyElim' :: Empty -> Elim' a -> Arg a
isApplyElim' e = fromMaybe (absurd e) . isApplyElim

-- | Only 'Apply' variant.
isProperApplyElim :: Elim' a -> Bool
isProperApplyElim = \case
  Apply _  -> True
  IApply{} -> False
  Proj{}   -> False

-- | Drop 'Apply' constructors. (Safe)
allApplyElims :: [Elim' a] -> Maybe [Arg a]
allApplyElims = mapM isApplyElim

-- | Split at first non-'Apply'
splitApplyElims :: [Elim' a] -> ([Arg a], [Elim' a])
splitApplyElims (Apply u : es) = mapFst (u :) $ splitApplyElims es
splitApplyElims es             = ([], es)

class IsProjElim e where
  isProjElim  :: e -> Maybe (ProjOrigin, QName)

instance IsProjElim (Elim' a) where
  isProjElim (Proj o d) = Just (o, d)
  isProjElim Apply{}    = Nothing
  isProjElim IApply{} = Nothing

-- | Discards @Proj f@ entries.
argsFromElims :: [Elim' t] -> [Arg t]
argsFromElims = mapMaybe isApplyElim

-- | Drop 'Proj' constructors. (Safe)
allProjElims :: [Elim' t] -> Maybe [(ProjOrigin, QName)]
allProjElims = mapM isProjElim

instance KillRange a => KillRange (Elim' a) where
  killRange = fmap killRange

instance Pretty tm => Pretty (Elim' tm) where
  prettyPrec p (Apply v)    = prettyPrec p v
  prettyPrec _ (Proj _o x)  = text ("." ++ prettyShow x)
  prettyPrec p (IApply x y r) = prettyPrec p r
--  prettyPrec p (IApply x y r) = text "@[" <> prettyPrec 0 x <> text ", " <> prettyPrec 0 y <> text "]" <> prettyPrec p r

instance NFData a => NFData (Elim' a) where
  rnf (Apply x) = rnf x
  rnf Proj{}    = ()
  rnf (IApply x y r) = rnf x `seq` rnf y `seq` rnf r
