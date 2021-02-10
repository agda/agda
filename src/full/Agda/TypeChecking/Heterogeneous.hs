{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Agda.TypeChecking.Heterogeneous where

import Prelude hiding (drop, length)

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
import Agda.TypeChecking.Substitute.Class (Subst)
import Agda.TypeChecking.Monad.Pure (PureTCM)
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)

import Agda.Utils.Dependent
import Agda.Utils.Monad
import Agda.Utils.Pretty
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
drop n = ContextHet . L.drop n . unContextHet

length :: ContextHet -> Int
length = L.length . unContextHet

(⊣::) :: [Dom (Name, Type)] -> ContextHet -> ContextHet
as ⊣:: ctx =  ContextHet ( fmap (fmap (fmap (SingleT . Het))) as <> unContextHet  ctx)

(!!!) :: ContextHet -> Int -> Maybe (Dom (Name, TwinT))
ctx !!! n = contextHetToList ctx Agda.Utils.List.!!! n

-- | Switch heterogeneous context to a specific side
flipContext :: (MonadAddContext m) => m a -> m a
flipContext = updateContext IdS flipHet

apT :: Applicative f => TwinT''' Bool f (a -> b) -> TwinT''' Bool f a -> TwinT''' Bool  f b
apT (SingleT f) (SingleT a) = SingleT (f <*> a)
apT (SingleT (H'Both f))  TwinT{necessary,twinPid,twinLHS,twinCompat,twinRHS} =
                    TwinT{necessary
                         ,twinPid
                         ,direction=DirEq
                         ,twinLHS=f <$> twinLHS
                         ,twinCompat=f <$> twinCompat
                         ,twinRHS=f <$> twinRHS
                         }
apT TwinT{necessary,twinPid,twinLHS,twinCompat,twinRHS} (SingleT (H'Both b)) =
                    TwinT{necessary
                         ,twinPid
                         ,direction=DirEq
                         ,twinLHS=($ b) <$> twinLHS
                         ,twinCompat=($ b) <$> twinCompat
                         ,twinRHS=($ b) <$> twinRHS
                         }

apT TwinT{necessary=n₁,twinPid=p₁,twinLHS=l₁,twinCompat=c₁,twinRHS=r₁}
      TwinT{necessary=n₂,twinPid=p₂,twinLHS=l₂,twinCompat=c₂,twinRHS=r₂} =
                    TwinT{necessary=n₁ && n₂
                         ,twinPid=p₁++p₂
                         ,direction=DirEq
                         ,twinLHS=    l₁ <*> l₂
                         ,twinCompat= c₁ <*> c₂
                         ,twinRHS=    r₁ <*> r₂
                         }
infixl 4 `apT`


pairT :: Applicative f => TwinT''' Bool f a ->
                          TwinT''' Bool f b ->
                          TwinT''' Bool f (a,b)
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

data a :∈ b = a :∈ b

pattern (:∋) :: forall a b. b -> a -> a :∈ b
pattern b :∋ a = a :∈ b
#if __GLASGOW_HASKELL__ >= 802
{-# COMPLETE (:∋) #-}
#endif

instance (AsTwin a, AsTwin b) => AsTwin (a :∈ b) where
  type AsTwin_ (a :∈ b) = AsTwin_ a :∈ AsTwin_ b
  asTwin (a :∈ b) = asTwin a :∈ asTwin b

---------------------------------------------------------------------------
-- * Twins
---------------------------------------------------------------------------

type SimplifyHetM m = (MonadTCEnv m, ReadTCState m, MonadAddContext m, MonadDebug m, MonadBlock m,
                       PureTCM m, HasBuiltins m)

class AsTwin a => IsTwinSolved a where
  blockOnTwin ::  (SimplifyHetM m) => a -> m Blocker
  isTwinSolved :: (SimplifyHetM m) => a -> m Bool
  isTwinSingle :: a -> Bool
  simplifyHet' :: (SimplifyHetM m) => a -> (Either a (AsTwin_ a) -> m b) -> m b

  isTwinSolved a = blockOnTwin a >>= \case
    AlwaysUnblock -> return True
    _             -> return False

  default simplifyHet' :: (SimplifyHetM m, TwinAt 'Compat a, AsTwin_ a ~ TwinAt_ 'Compat a) =>
                          a -> (Either a (AsTwin_ a) -> m b) -> m b
  simplifyHet' b κ = isTwinSolved b >>= \case
    False -> κ (Left b)
    True  -> κ (Right (twinAt @'Compat b))

instance IsTwinSolved (TwinT' a) where
  blockOnTwin SingleT{}      = return AlwaysUnblock
  blockOnTwin TwinT{twinPid} = unblockOnAll . Set.fromList . map UnblockOnProblem <$> filterM (fmap not . isProblemSolved) twinPid

  isTwinSolved SingleT{}      = return True
  isTwinSolved TwinT{twinPid} = allM twinPid isProblemSolved

  isTwinSingle SingleT{} = True
  isTwinSingle TwinT{}   = False

instance IsTwinSolved a => IsTwinSolved (Dom a) where
  blockOnTwin = blockOnTwin . unDom
  isTwinSolved = isTwinSolved . unDom
  isTwinSingle = isTwinSingle . unDom
  simplifyHet' dom κ = simplifyHet' (unDom dom) $ \a ->
    κ (bimap (\x -> dom{unDom=x}) (\x -> dom{unDom=x}) a)

instance IsTwinSolved a => IsTwinSolved (CompareAs' a) where
  blockOnTwin (AsTermsOf a) = blockOnTwin a
  blockOnTwin AsTypes       = return AlwaysUnblock
  blockOnTwin AsSizes       = return AlwaysUnblock

  isTwinSolved (AsTermsOf a) = isTwinSolved a
  isTwinSolved AsTypes       = return True
  isTwinSolved AsSizes       = return True

  simplifyHet' (AsTermsOf a) κ = simplifyHet' a $ \a -> κ (bimap AsTermsOf AsTermsOf a)
  simplifyHet' AsTypes       κ = κ (Right AsTypes)
  simplifyHet' AsSizes       κ = κ (Right AsSizes)

  isTwinSingle (AsTermsOf a) = isTwinSingle a
  isTwinSingle AsTypes       = True
  isTwinSingle AsSizes       = True

instance IsTwinSolved Name where
  blockOnTwin _  = pure AlwaysUnblock
  isTwinSolved _ = pure True
  simplifyHet' n κ = κ (Right n)
  isTwinSingle _ = True

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a,b) where
  blockOnTwin  (a,b) = unblockOnBoth <$> blockOnTwin a <*> blockOnTwin b
  isTwinSolved (a,b) = andM [isTwinSolved b, isTwinSolved a]
  simplifyHet' (a,b) κ =
    simplifyHet' a $ \a ->
      simplifyHet' b $ \b ->
        case (a,b) of
          (Right a, Right b) -> κ$ Right (a, b)
          ( Left a, Right b) -> κ$ Left  (a, asTwin b)
          (Right a,  Left b) -> κ$ Left  (asTwin a, b)
          ( Left a,  Left b) -> κ$ Left  (a, b)
  isTwinSingle (a,b) = isTwinSingle a && isTwinSingle b

instance IsTwinSolved () where
  blockOnTwin ()  = pure AlwaysUnblock
  isTwinSolved () = pure True
  simplifyHet' () κ = κ (Right ())
  isTwinSingle () = True

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a :∈ b) where
  blockOnTwin  (b :∋ a) = unblockOnBoth <$> blockOnTwin b <*> blockOnTwin a
  isTwinSolved (b :∋ a) = andM [isTwinSolved b, isTwinSolved a]
  isTwinSingle (b :∋ a) = isTwinSingle b && isTwinSingle a
  simplifyHet' (b :∋ a) κ = simplifyHet' b $ \case
    Right b -> simplifyHet' a $ \case
      Right a -> κ (Right (a :∈ b))
      Left  a -> κ (Left  (a :∈ asTwin b))
    Left  b -> κ (Left (a :∈ b))

instance (IsTwinSolved a, Subst a) => IsTwinSolved (Abs a) where
  blockOnTwin = blockOnTwin . unAbs
  isTwinSolved = isTwinSolved . unAbs
  isTwinSingle = isTwinSingle . unAbs
  simplifyHet' abs κ =
    κ =<< (underAbstraction_ abs $ \a ->
      simplifyHet' a $ \a ->
        return $ bimap (\x -> abs{unAbs=x}) (\x -> abs{unAbs=x}) a)

newtype AttemptConversion a = AttemptConversion { attemptConversion :: a }

instance AsTwin a => AsTwin (AttemptConversion a) where
  type AsTwin_ (AttemptConversion a) = AsTwin_ a
  asTwin = AttemptConversion . asTwin

instance TwinAt s a => TwinAt s (AttemptConversion a) where
  type TwinAt_ s (AttemptConversion a) = TwinAt_ s a
  twinAt = twinAt @s . attemptConversion

instance (AsTwin a, IsTwinSolved (AttemptConversion a)) => IsTwinSolved (AttemptConversion (Dom a)) where
  blockOnTwin  = blockOnTwin  . fmap AttemptConversion . attemptConversion
  isTwinSolved = isTwinSolved . fmap AttemptConversion . attemptConversion
  simplifyHet' (AttemptConversion b) κ = simplifyHet' (fmap AttemptConversion b) $ \e -> κ $ bimap coerce id e
  isTwinSingle = isTwinSingle . fmap AttemptConversion . attemptConversion

instance IsTwinSolved (AttemptConversion Name) where
  blockOnTwin  = blockOnTwin  . attemptConversion
  isTwinSolved = isTwinSolved . attemptConversion
  simplifyHet' (AttemptConversion b) κ = simplifyHet' b $ \e -> κ $ bimap AttemptConversion id e
  isTwinSingle = isTwinSingle . attemptConversion

instance (AsTwin a, AsTwin b, IsTwinSolved (AttemptConversion a), IsTwinSolved (AttemptConversion b)) =>
         IsTwinSolved (AttemptConversion (a,b)) where
  blockOnTwin  = blockOnTwin  . bimap AttemptConversion AttemptConversion . attemptConversion
  isTwinSolved = isTwinSolved . bimap AttemptConversion AttemptConversion . attemptConversion
  simplifyHet' (AttemptConversion b) κ = simplifyHet' (bimap AttemptConversion AttemptConversion b) $ \e -> κ $ bimap coerce id e
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


striveWithEffort :: (MonadDebug m, MonadTCEnv m) =>
  Nat -> (Blocker -> m a) -> m a -> m a
striveWithEffort n postpone doIt =
  strive (EffortLevel (NatExt n)) >>= \case
        Doable        -> doIt
        ExtraEffort e -> do
          reportSLn "tc.constr.effort" 20 $ "Extra " <> prettyShow e <> " required; postponing"
          postpone (unblockOnEffort e)

type SimplifyHet a = (IsTwinSolved a)

-- TODO: One could also check free variables and strengthen the
-- context, but this is supposed to be a cheap operation
simplifyHetFull, simplifyHet :: forall a c m. (SimplifyHetM m, SimplifyHet a) => a -> (a -> m c) -> m c
-- simplifyHetFull b κ = go Empty =<< getContext_
--   where
--     go acc Empty =
--       unsafeModifyContext {- IdS -} (const acc) $ isTwinSolved b >>= \case
--                   True  -> κ (asTwin$ twinAt @'Compat b)
--                   False -> κ b
--     go acc ctx@(a :⊢: γΓ)  =
--       isTwinSolved a >>= \case
--         True  -> go (acc :⊢ (asTwin$ twinAt @'Compat a)) γΓ
--         False -> unsafeModifyContext {- IdS -} (const (acc ⊢:: ctx)) $ κ b
--
simplifyHetFull b κ = do
  γΓ <- getContext_
  go γΓ $ \isHomo γΓ' ->
    unsafeModifyContext {- IdS -} (const γΓ') $
      case isHomo of
        True  -> simplifyHet' b $ \case
                  Right b'  -> κ (asTwin b')
                  Left  b   -> κ b
        False -> κ b
  where
    go Empty κ = κ True Empty
    go (γΓ :⊢ a) κ =
      go γΓ $ \isHomo γΓ' ->
        case isHomo of
          True -> simplifyHet' a $ \case
            Right a' -> κ True  (γΓ' :⊢ asTwin a')
            Left  a  -> κ False (γΓ' :⊢ a)
          False -> κ False (γΓ' :⊢ a)

simplifyHet b κ = do
  case isTwinSingle b of
    True  -> κ b
    False -> simplifyHet' b $ \case
      Left  b -> κ b
      Right b' -> do
        γΓ <- getContext_
        go γΓ $ \case
          Nothing  -> κ b
          Just γΓ' -> unsafeModifyContext {- IdS -} (const γΓ') $ κ (asTwin b')
  where
    go Empty κ = κ (Just Empty)
    go (γΓ :⊢ a) κ =
      simplifyHet' a $ \case
        Left{}    -> κ Nothing
        Right a'  -> do
          go γΓ $ \case
            Nothing  -> κ Nothing
            Just γΓ' -> κ (Just (γΓ' :⊢ asTwin a'))

-- | Remove unnecessary twins from the context
-- simplifyContextHet :: SimplifyHetM m => m a -> m a
-- simplifyContextHet m = simplifyHet () (\() -> m)

------------------------------------------------------------------
-- Distributing instances
------------------------------------------------------------------

class Commute f g where
  commute  :: f (g a) -> (g (f a))

class CommuteM f g where
  type CommuteMonad f g (m :: K.Type -> K.Type) :: K.Constraint
  commuteM  :: (CommuteMonad f g m) => f (g a) -> m (g (f a))

instance Commute (Het s) Abs where
  commute :: Het s (Abs a) -> Abs (Het s a)
  commute = Data.Coerce.coerce

instance Commute (Het s) Elim' where
  commute :: Het s (Elim' a) -> Elim' (Het s a)
  commute = Data.Coerce.coerce

instance Commute Elim' (Het s) where
  commute = Data.Coerce.coerce

instance Commute (Het s) [] where
  commute :: Het s [a] -> [Het s a]
  commute = Data.Coerce.coerce

instance Commute [] (Het s) where
  commute = Data.Coerce.coerce

instance Commute (Het s) Maybe where
  commute = Data.Coerce.coerce

instance Commute Maybe (Het s) where
  commute = Data.Coerce.coerce

instance Commute (Het s) ((,) a) where
  commute :: Het s (a,b) -> (a, Het s b)
  commute = Data.Coerce.coerce

instance Commute (Het s) Arg where commute = Data.Coerce.coerce
instance Commute Arg (Het s) where commute = Data.Coerce.coerce

instance Functor f => Commute Abs (TwinT''' b f) where
  commute (Abs name x)   = Abs name <$> x
  commute (NoAbs name x) = NoAbs name <$> x

