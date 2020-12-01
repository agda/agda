{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Heterogeneous where

import Prelude hiding (drop, length)

import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Data.Sequence as S

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Dependent
import Agda.Utils.Monad
import Agda.Utils.Pretty
import qualified Agda.Utils.List

import Agda.Utils.Impossible

----------------------------------------------------------------------
-- * Data structure for a twin type
----------------------------------------------------------------------

--data WithHet' c a = WithHet c a
--type WithHet a = WithHet' ContextHet a

instance Pretty a => Pretty (TwinT' a) where
  pretty (SingleT a) = pretty a
  pretty (TwinT{twinPid,necessary,twinLHS=a,twinRHS=b}) =
    pretty a <> "‡"
             <> (if necessary then "" else "*")
             <> pretty twinPid
             <> pretty b

instance TwinAt s Term where twinAt = id
instance TwinAt s Type where twinAt = id

instance TwinAt s a => TwinAt s (Maybe a) where
  type TwinAt_ s (Maybe a) = Maybe (TwinAt_ s a)
  twinAt = fmap (twinAt @s)

{-# INLINE commuteHet #-}
commuteHet :: (Coercible (f a) (f (Het s a))) => Het s (f a) -> f (Het s a)
commuteHet = coerce . unHet

class FlipHet a where
  type FlippedHet a
  type FlippedHet a = a

  flipHet :: a -> FlippedHet a

instance FlipHet (Het 'LHS a) where
  type FlippedHet (Het 'LHS a) = (Het 'RHS a)
  flipHet = coerce

instance FlipHet (Het 'RHS a) where
  type FlippedHet (Het 'RHS a) = (Het 'LHS a)
  flipHet = coerce

instance FlipHet (Het 'Both a) where
  flipHet = id

instance FlipHet TwinT where
  flipHet a@SingleT{} = a
  flipHet TwinT{twinLHS,twinRHS,twinPid,direction,necessary,twinCompat} =
    TwinT{twinLHS=flipHet twinRHS,
          twinRHS=flipHet twinLHS,
          direction=flipHet direction,
          twinCompat,
          necessary,
          twinPid}

instance FlipHet ContextHet where
  flipHet (ContextHet ctx) = ContextHet$ fmap (fmap (fmap flipHet)) ctx

instance FlipHet Term where flipHet = id
instance FlipHet Type where flipHet = id
instance FlipHet ()   where flipHet = id

instance FlipHet a => FlipHet (CompareAs' a) where
   type FlippedHet (CompareAs' a) = CompareAs' (FlippedHet a)
   flipHet = fmap flipHet

instance (FlipHet a, FlipHet b) => FlipHet (a, b) where
  type FlippedHet (a, b) = (FlippedHet a, FlippedHet b)
  flipHet (a,b) = (flipHet a, flipHet b)

instance (FlipHet a, FlipHet b, FlipHet c) => FlipHet (a, b, c) where
  type FlippedHet (a, b, c) = (FlippedHet a, FlippedHet b, FlippedHet c)
  flipHet (a,b,c) = (flipHet a, flipHet b, flipHet c)

data HetP a = HetP (Het 'LHS a) (Het 'RHS a)
instance FlipHet (HetP a) where
  flipHet (HetP a b) = HetP (flipHet b) (flipHet a)

instance FlipHet CompareDirection where
  type FlippedHet CompareDirection = CompareDirection
  flipHet = flipCmp

-- errorInContextHet :: forall het. (Sing het) => If_ het ContextHet () -> TypeError -> TypeError
-- errorInContextHet ctx = case sing :: SingT het of
--  STrue  -> ErrorInContextHet (unIf ctx)
--  SFalse -> case ctx of If () -> id

{-# INLINE dirToCmp_ #-}
dirToCmp_ :: forall s₁ s₂ m t a c. (FlipHet t, FlippedHet t ~ t, MonadAddContext m, AreSides s₁ s₂) =>
             (Comparison -> t -> Het 'LHS a -> Het 'RHS a -> m c) ->
              CompareDirection -> t -> Het s₁ a -> Het s₂ a -> m c
dirToCmp_ κ dir a u v = go sing sing dir
  where
    go :: SingT s₁ -> SingT s₂ -> CompareDirection -> m c
    go SLHS SRHS DirGeq = flipContext$ κ CmpLeq (flipHet a) (flipHet v) (flipHet u)
    go SLHS SRHS DirEq  = κ CmpEq  a u v
    go SLHS SRHS DirLeq = κ CmpLeq a u v
    go SRHS SLHS DirGeq = κ CmpLeq a v u
    go SRHS SLHS DirEq  = flipContext$ κ CmpEq  (flipHet a) (flipHet u) (flipHet v)
    go SRHS SLHS DirLeq = flipContext$ κ CmpLeq (flipHet a) (flipHet u) (flipHet v)

drop :: Int -> ContextHet -> ContextHet
drop n = ContextHet . S.drop n . unContextHet

length :: ContextHet -> Int
length = S.length . unContextHet

(⊣::) :: [Dom (Name, Type)] -> ContextHet -> ContextHet
as ⊣:: ctx =  ContextHet ( fmap (fmap (fmap (SingleT . Het))) (S.fromList as) <> unContextHet  ctx)

(!!!) :: ContextHet -> Int -> Maybe (Dom (Name, TwinT))
ctx !!! n = contextHetToList ctx Agda.Utils.List.!!! n

-- | Switch heterogeneous context to a specific side
flipContext :: (MonadAddContext m) => m a -> m a
flipContext = updateContext IdS flipHet


--  a `isBuiltin` builtinLevel >>= \case
--   True  -> return TLevel
--   False -> case a of
--     Pi a b   -> return (Pi a b)
--     Lam{}    -> return TLam
--     Def q es -> return (TDef q (asTwin es))
--     _        -> return TUnknown
--
-- typeView (TwinT{twinPid,necessary,direction,twinLHS,twinRHS}) = a `isBuiltin` builtinLevel >>= \case
--   True  -> return TLevel
--   False -> case (twinLHS,twinRHS) of
--     (Pi a₁ b₁, Pi a₂ b₂)   -> do
--
--
--       return (Pi (TwinTa b)
--     Lam{}    -> return TLam
--     Def q es -> return (TDef q (asTwin es))
--     _        -> return TUnknown
--
