{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Agda.TypeChecking.Heterogeneous where

import Prelude hiding (drop, length, splitAt)

import Control.Monad (filterM)
import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Bifunctor (bimap)
import qualified Data.Kind as K
import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Data.Sequence as S
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common (Nat, Arg)
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Position

import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Constraints
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute.Class (Subst)
import Agda.TypeChecking.Monad.Pure (PureTCM)
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)

import Agda.Utils.Dependent
import Agda.Utils.Functor ((<&>))
import Agda.Utils.IntSet.Typed (ISet)
import qualified Agda.Utils.IntSet.Typed as ISet
import Agda.Utils.Monad
import Agda.Utils.Pretty (Pretty)
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.List

import Agda.Utils.Impossible
import qualified Data.List as L

----------------------------------------------------------------------
-- * Data structure for a twin type
----------------------------------------------------------------------

--data WithHet' c a = WithHet c a
--type WithHet a = WithHet' ContextHet a

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
  flipHet TwinT{twinLHS,twinRHS,twinPid,direction,necessary} =
    TwinT{twinLHS=flipHet twinRHS,
          twinRHS=flipHet twinLHS,
          direction=flipHet direction,
          necessary,
          twinPid}

instance FlipHet ContextHet where
  flipHet ctx = fmap (fmap (fmap flipHet)) ctx

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

drop :: Int -> Context_ -> Context_
drop n x         | n <= 0 = x
drop _ Empty              = Empty
drop n (_ :⊣ γΓ)          = drop (n-1) γΓ

length :: Context_ -> Int
length Empty = 0
length (_ :⊣ γΓ)  = 1 + length γΓ

splitAt :: Int -> Context_ -> [Dom (Name, TwinT)] :∈ Context_
splitAt n γΓ | n <= 0 = [] :∈ γΓ
splitAt _ Empty       = [] :∈ Empty
splitAt n (a :⊣ γΓ)   = (a:as) :∈ γΓ'
  where as :∈ γΓ' = splitAt (n-1) γΓ


(!!!) :: ContextHet -> Int -> Maybe (Dom (Name, TwinT))
ctx !!! n = contextHetToList ctx Agda.Utils.List.!!! n

-- | Switch heterogeneous context to a specific side
flipContext :: (MonadAddContext m) => m a -> m a
flipContext = updateContext IdS flipHet

-- TODO Víctor 2021-03-03: What should the direction be?
apT :: TwinT'' Bool (a -> b) -> TwinT'' Bool a -> TwinT'' Bool b
apT (SingleT f) (SingleT a) = SingleT (f <*> a)
apT (SingleT (OnBoth f))  TwinT{necessary,twinPid,twinLHS,twinRHS} =
                    TwinT{necessary
                         ,twinPid
                         ,direction=DirEq
                         ,twinLHS=f <$> twinLHS
                         ,twinRHS=f <$> twinRHS
                         }
apT TwinT{necessary,twinPid,twinLHS,twinRHS} (SingleT (OnBoth b)) =
                    TwinT{necessary
                         ,twinPid
                         ,direction=DirEq
                         ,twinLHS=($ b) <$> twinLHS
                         ,twinRHS=($ b) <$> twinRHS
                         }

apT TwinT{necessary=n₁,twinPid=p₁,twinLHS=l₁,twinRHS=r₁}
      TwinT{necessary=n₂,twinPid=p₂,twinLHS=l₂,twinRHS=r₂} =
                    TwinT{necessary=n₁ && n₂
                         ,twinPid=p₁ `ISet.union` p₂
                         ,direction=DirEq
                         ,twinLHS=    l₁ <*> l₂
                         ,twinRHS=    r₁ <*> r₂
                         }
infixl 4 `apT`


pairT :: TwinT'' Bool a -> TwinT'' Bool b -> TwinT'' Bool (a,b)
pairT a b = (,) <$> a `apT` b



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

---------------------------------------------------------------------------
-- * Twins
---------------------------------------------------------------------------

type SimplifyHetM m = (MonadTCEnv m, ReadTCState m, MonadAddContext m, MonadDebug m, MonadBlock m,
                       PureTCM m, HasBuiltins m)

-- TODO Víctor 2021-03-03: This is over-engineered
class AsTwin a => IsTwinSolved a where
  blockOnTwin ::  (SimplifyHetM m) => a -> m Blocker
  isTwinSolved :: (SimplifyHetM m) => a -> m Bool
  isTwinSingle :: a -> Bool
  simplifyHet' :: (SimplifyHetM m) => a -> m (Either a (AsTwin_ a))

--  isTwinSolved a = blockOnTwin a >>= \case
--    AlwaysUnblock -> return True
--    _             -> return False

--  default simplifyHet' :: (SimplifyHetM m, TwinAt 'Compat a, AsTwin_ a ~ TwinAt_ 'Compat a) =>
--                        a -> (Either a (AsTwin_ a) -> m b) -> m b
--  simplifyHet' b κ = isTwinSolved b >>= \case
--    False -> κ (Left b)
--    True  -> κ (Right (twinAt @'Compat b))

instance IsTwinSolved (ISet ProblemId) where
  blockOnTwin pids    = unblockOnAll . Set.fromList . map UnblockOnProblem . ISet.toList <$> keepUnsolvedProblems pids
  isTwinSolved        = areAllProblemsSolved
  isTwinSingle        = const False
  simplifyHet' pids   = keepUnsolvedProblems pids <&> \case
    x | ISet.null x -> Right ()
      | otherwise   -> Left x

instance IsTwinSolved (TwinT' a) where
  blockOnTwin = blockOnTwin . getPids
  isTwinSolved = isTwinSolved . getPids
  isTwinSingle SingleT{} = True
  isTwinSingle TwinT{}   = False
  simplifyHet' (SingleT b) = pure (Right (twinAt @'Single b))
  simplifyHet' b@TwinT{twinPid} =
    simplifyHet' twinPid <&> \case
      Right ()       -> Right$ twinAt @'Single b{twinPid=mempty}
      Left  twinPid' -> Left$  b{twinPid=twinPid'}

instance IsTwinSolved a => IsTwinSolved (Dom a) where
  blockOnTwin = blockOnTwin . unDom
  isTwinSolved = isTwinSolved . unDom
  isTwinSingle = isTwinSingle . unDom
  simplifyHet' dom = simplifyHet' (unDom dom) <&> \a ->
    bimap (\x -> dom{unDom=x}) (\x -> dom{unDom=x}) a

instance IsTwinSolved a => IsTwinSolved (CompareAs' a) where
  blockOnTwin (AsTermsOf a) = blockOnTwin a
  blockOnTwin AsTypes       = return AlwaysUnblock
  blockOnTwin AsSizes       = return AlwaysUnblock

  isTwinSolved (AsTermsOf a) = isTwinSolved a
  isTwinSolved AsTypes       = return True
  isTwinSolved AsSizes       = return True

  simplifyHet' (AsTermsOf a) = simplifyHet' a <&> \a -> bimap AsTermsOf AsTermsOf a
  simplifyHet' AsTypes       = pure (Right AsTypes)
  simplifyHet' AsSizes       = pure (Right AsSizes)

  isTwinSingle (AsTermsOf a) = isTwinSingle a
  isTwinSingle AsTypes       = True
  isTwinSingle AsSizes       = True

instance IsTwinSolved Name where
  blockOnTwin _  = pure AlwaysUnblock
  isTwinSolved _ = pure True
  simplifyHet' n = pure (Right n)
  isTwinSingle _ = True

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a,b) where
  blockOnTwin  (a,b) = unblockOnBoth <$> blockOnTwin a <*> blockOnTwin b
  isTwinSolved (a,b) = andM [isTwinSolved b, isTwinSolved a]
  simplifyHet' (a,b) =
    simplifyHet' a >>= \a ->
      simplifyHet' b <&> \b ->
        case (a,b) of
          (Right a, Right b) -> Right (a, b)
          ( Left a, Right b) -> Left  (a, asTwin b)
          (Right a,  Left b) -> Left  (asTwin a, b)
          ( Left a,  Left b) -> Left  (a, b)
  isTwinSingle (a,b) = isTwinSingle a && isTwinSingle b

instance IsTwinSolved () where
  blockOnTwin ()  = pure AlwaysUnblock
  isTwinSolved () = pure True
  simplifyHet' () = pure (Right ())
  isTwinSingle () = True

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a :∈ b) where
  blockOnTwin  (b :∋ a) = unblockOnBoth <$> blockOnTwin b <*> blockOnTwin a
  isTwinSolved (b :∋ a) = andM [isTwinSolved b, isTwinSolved a]
  isTwinSingle (b :∋ a) = isTwinSingle b && isTwinSingle a
  simplifyHet' (b :∋ a) = simplifyHet' b >>= \case
    Right b -> simplifyHet' a <&> \case
      Right a -> Right (a :∈ b)
      Left  a -> Left  (a :∈ asTwin b)
    Left  b -> pure$ Left (a :∈ b)

instance (IsTwinSolved a, Subst a) => IsTwinSolved (Abs a) where
  blockOnTwin = blockOnTwin . unAbs
  isTwinSolved = isTwinSolved . unAbs
  isTwinSingle = isTwinSingle . unAbs
  simplifyHet' abs =
    underAbstraction_ abs $ \a ->
      simplifyHet' a <&> \a ->
        bimap (\x -> abs{unAbs=x}) (\x -> abs{unAbs=x}) a

newtype AttemptConversion a = AttemptConversion { attemptConversion :: a }

instance AsTwin a => AsTwin (AttemptConversion a) where
  type AsTwin_ (AttemptConversion a) = AsTwin_ a
  asTwin = AttemptConversion . asTwin

instance AsTwin (ISet ProblemId) where
  type AsTwin_ (ISet ProblemId) = ()
  asTwin () = ISet.empty

instance TwinAt s a => TwinAt s (AttemptConversion a) where
  type TwinAt_ s (AttemptConversion a) = TwinAt_ s a
  twinAt = twinAt @s . attemptConversion

instance (AsTwin a, IsTwinSolved (AttemptConversion a)) => IsTwinSolved (AttemptConversion (Dom a)) where
  blockOnTwin  = blockOnTwin  . fmap AttemptConversion . attemptConversion
  isTwinSolved = isTwinSolved . fmap AttemptConversion . attemptConversion
  simplifyHet' (AttemptConversion b) = simplifyHet' (fmap AttemptConversion b) <&> \e ->
    bimap coerce id e
  isTwinSingle = isTwinSingle . fmap AttemptConversion . attemptConversion

instance IsTwinSolved (AttemptConversion Name) where
  blockOnTwin  = blockOnTwin  . attemptConversion
  isTwinSolved = isTwinSolved . attemptConversion
  simplifyHet' (AttemptConversion b) = simplifyHet' b <&> \e -> bimap AttemptConversion id e
  isTwinSingle = isTwinSingle . attemptConversion

instance (AsTwin a, AsTwin b, IsTwinSolved (AttemptConversion a), IsTwinSolved (AttemptConversion b)) =>
         IsTwinSolved (AttemptConversion (a,b)) where
  blockOnTwin  = blockOnTwin  . bimap AttemptConversion AttemptConversion . attemptConversion
  isTwinSolved = isTwinSolved . bimap AttemptConversion AttemptConversion . attemptConversion
  simplifyHet' (AttemptConversion b) = simplifyHet' (bimap AttemptConversion AttemptConversion b)
    <&> \e -> bimap coerce id e
  isTwinSingle = isTwinSingle . bimap AttemptConversion AttemptConversion . attemptConversion

instance IsTwinSolved (AttemptConversion TwinT) where
  isTwinSingle = isTwinSingle . attemptConversion

  blockOnTwin (AttemptConversion t) = do
    blockOnTwin t >>= \case
      AlwaysUnblock -> return AlwaysUnblock
      bs -> striveWithEffort 10 (return . unblockOnEither bs) $
              case t of
                TwinT{direction,twinLHS,twinRHS} ->
                  (`unblockOnEither` bs) <$>
                  runPureConversion (compareTypeDir_ direction twinLHS twinRHS)
                _ -> __IMPOSSIBLE__

  isTwinSolved (AttemptConversion t) = do
    isTwinSolved t >>= \case
      True  -> return True
      False -> striveWithEffort 10 (return . const False) $
                 case t of
                   TwinT{direction,twinLHS,twinRHS} ->
                       runPureConversion' (compareTypeDir_ direction twinLHS twinRHS)
                   _ -> __IMPOSSIBLE__

  simplifyHet' (AttemptConversion t) = do
    simplifyHet' t >>= \case
      Right a  -> pure $ Right a
      Left  t' -> striveWithEffort 10 (const (pure (Left (AttemptConversion t')))) $
                    case t' of
                      TwinT{direction,twinLHS,twinRHS} ->
                        runPureConversion' (compareTypeDir_ direction twinLHS twinRHS) <&> \case
                          True  -> Right $ twinAt @'Single t'{twinPid=mempty}
                          False -> Left (AttemptConversion t')
                      _ -> __IMPOSSIBLE__

striveWithEffort :: (MonadDebug m, MonadTCEnv m) =>
  Nat -> (Blocker -> m a) -> m a -> m a
striveWithEffort n postpone doIt =
  strive (EffortLevel (NatExt n)) >>= \case
        Doable        -> doIt
        ExtraEffort e -> do
          reportSDoc "tc.constr.effort" 20 $ "Extra" <+> pretty e <+> "required; postponing"
          postpone (unblockOnEffort e)

instance IsTwinSolved Context_ where
  blockOnTwin  = blockOnTwin . getPids
  isTwinSolved = isTwinSolved . getPids
  isTwinSingle = const False
  simplifyHet' Empty           = pure (Right [])
  simplifyHet' ctx@(Entry bs a) =
    simplifyHet' bs <&> \case
      Right ()  -> Right $ twinAt @'Single (MarkAsSolved ctx)
      Left  bs' -> Left  $ Entry bs' a

type SimplifyTwin a = (IsTwinSolved a, Pretty a, Pretty (AsTwin_ a))
type SimplifyTwinM m = (MonadBlock m, PureTCM m)

-- | Simplifies a twin type provided that the associated problems are solved,
--   and that the problems associated with the context are solved (in that case,
--   it will also simplify the context)
simplifyTwin :: (SimplifyTwin a, SimplifyTwinM m) => a -> (a -> m b) -> m b
simplifyTwin b κ = do
  reportSDoc "tc.conv.het" 80 $ "Simplifying" <+> pretty b
  case isTwinSingle b of
    True  -> κ b
    False -> simplifyHet' b >>= \case
      Left  b -> κ b
      Right b' -> do
        γΓ_ <- getContext_
        simplifyHet' γΓ_ >>= \case
          -- Víctor (2021-03-05):
          -- This removes those problem ids that are already solved
          -- from the context
          Left γΓ_ -> do
            reportSDoc "tc.conv.het" 80 $ "context not homogeneous, can't simplify"
            unsafeModifyContext (const γΓ_) $ κ b
          Right γΓ -> do
            reportSDoc "tc.conv.het" 80 $ "success:" <+> pretty b'
            -- Víctor (2021-03-05): The context is now single sided.
            -- We replace it with its single-sided version.
            unsafeModifyContext (const $ asTwin γΓ) $ κ (asTwin b')

-- | Remove unnecessary twins from the context
simplifyContext_ :: SimplifyTwinM m => m a -> m a
simplifyContext_ m = simplifyTwin () (\() -> m)

