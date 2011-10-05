{-# LANGUAGE DeriveDataTypeable #-}
-- | Epic interface data structure, which is serialisable and stored for each
--   compiled file
module Agda.Compiler.Epic.Interface where

import Control.Monad

import Data.Function
import qualified Data.Map as M
import Data.Map(Map)
import Data.Monoid
import qualified Data.Set as S
import Data.Set(Set)
import Data.Typeable

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Internal

type Var       = String
data Tag       = Tag Int
               | PrimTag Var
  deriving (Show, Eq, Ord, Typeable)

data Forced = NotForced | Forced
  deriving (Show, Typeable, Eq)

-- | Filter a list using a list of Bools specifying what to keep.
pairwiseFilter :: [Bool] -> [a] -> [a]
pairwiseFilter (True :bs) (a:as) = a : pairwiseFilter bs as
pairwiseFilter (False:bs) (_:as) = pairwiseFilter bs as
pairwiseFilter _           _     = []

notForced :: ForcedArgs -> [a] -> [a]
notForced = pairwiseFilter . map (== NotForced)

forced :: ForcedArgs -> [a] -> [a]
forced = pairwiseFilter . map (== Forced)

data Relevance
  = Irr
  | Rel
  deriving (Eq, Ord, Show, Typeable)

type ForcedArgs   = [Forced]
type RelevantArgs = [Relevance]

data InjectiveFun = InjectiveFun
  { injArg     :: Nat
  , injArity   :: Nat
  }
  deriving (Show, Typeable, Eq)

data EInterface = EInterface
    { constrTags    :: Map QName Tag
    , definitions   :: Set Var
    , defDelayed    :: Map QName Bool
    , conArity      :: Map QName Int
    , mainName      :: Maybe QName
    , relevantArgs  :: Map Var   RelevantArgs
    , forcedArgs    :: Map QName ForcedArgs
    , injectiveFuns :: Map QName InjectiveFun
    } deriving (Typeable, Show)

instance Monoid EInterface where
  mempty = EInterface
      { constrTags    = mempty
      , definitions   = mempty
      , defDelayed    = mempty
      , conArity      = mempty
      , mainName      = Nothing
      , relevantArgs  = mempty
      , forcedArgs    = mempty
      , injectiveFuns = mempty
      }
  mappend x y = EInterface
      { constrTags    = comb constrTags
      , definitions   = comb definitions
      , defDelayed    = comb defDelayed
      , conArity      = comb conArity
      , mainName      = mainName x `mplus` mainName y
      , relevantArgs  = comb relevantArgs
      , forcedArgs    = comb forcedArgs
      , injectiveFuns = comb injectiveFuns
      }
    where
      comb :: Monoid a => (EInterface -> a) -> a
      comb f = (mappend `on` f) x y
