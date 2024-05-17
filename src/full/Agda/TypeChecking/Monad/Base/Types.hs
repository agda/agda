-- | Data structures for the type checker.
--
-- Part of "Agda.TypeChecking.Monad.Base", extracted to avoid import cycles.

module Agda.TypeChecking.Monad.Base.Types where

import Control.DeepSeq
import GHC.Generics

import Agda.Syntax.Internal
import Agda.Syntax.Common (LensArgInfo(..), LensModality, LensRelevance, LensCohesion, LensOrigin, LensQuantity, LensHiding)

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

-- | The @Context@ is a stack of 'ContextEntry's.
type Context      = [ContextEntry]
data ContextEntry
  = CtxVar Name (Dom Type)
  | CtxLet Name (Dom Type) Term
  deriving (Show, Generic)

isCtxVar :: ContextEntry -> Maybe (Name, Dom Type)
isCtxVar (CtxVar x a) = Just (x,a)
isCtxVar CtxLet{} = Nothing

isCtxLet :: ContextEntry -> Maybe (Name, Dom Type, Term)
isCtxLet CtxVar{} = Nothing
isCtxLet (CtxLet x a v) = Just (x,a,v)

instance LensArgInfo ContextEntry where
  getArgInfo (CtxVar _ a) = getArgInfo a
  getArgInfo (CtxLet _ a _) = getArgInfo a
  mapArgInfo f (CtxVar x a) = CtxVar x $ mapArgInfo f a
  mapArgInfo f (CtxLet x a v) = CtxLet x (mapArgInfo f a) v

instance LensModality ContextEntry where
instance LensRelevance ContextEntry where
instance LensCohesion ContextEntry where
instance LensOrigin ContextEntry where
instance LensQuantity ContextEntry where
instance LensHiding ContextEntry where

instance NFData ContextEntry

-- Feel free to move more types from Agda.TypeChecking.Monad.Base here when needed...
