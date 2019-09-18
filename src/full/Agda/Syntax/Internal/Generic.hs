{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP          #-}

-- | Tree traversal for internal syntax.

module Agda.Syntax.Internal.Generic where

#if __GLASGOW_HASKELL__ < 804
import Data.Monoid ((<>))
#endif
import Agda.Syntax.Common
import Agda.Syntax.Internal

-- | Generic term traversal.
--
--   Note: ignores sorts in terms!
--   (Does not traverse into or collect from them.)

class TermLike a where

  -- | Generic traversal with post-traversal action.
  --   Ignores sorts.
  traverseTermM :: Monad m => (Term -> m Term) -> a -> m a

  default traverseTermM :: (Monad m, Traversable f, TermLike b, f b ~ a)
                        => (Term -> m Term) -> a -> m a

  traverseTermM = traverse . traverseTermM

  -- | Generic fold, ignoring sorts.
  foldTerm :: Monoid m => (Term -> m) -> a -> m

  default foldTerm
    :: (Monoid m, Foldable f, TermLike b, f b ~ a) => (Term -> m) -> a -> m
  foldTerm = foldMap . foldTerm

-- Constants

instance TermLike Bool where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Int where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Integer where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Char where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike QName where
  traverseTermM _ = pure
  foldTerm _      = mempty

-- Functors

instance TermLike a => TermLike (Elim' a)      where
instance TermLike a => TermLike (Arg a)        where
instance TermLike a => TermLike (Dom a)        where
instance TermLike a => TermLike [a]            where
instance TermLike a => TermLike (Maybe a)      where
instance TermLike a => TermLike (Abs a)        where
instance TermLike a => TermLike (Blocked a)    where
instance TermLike a => TermLike (Tele a)       where
instance TermLike a => TermLike (WithHiding a) where

-- Tuples

instance (TermLike a, TermLike b) => TermLike (a, b) where
  traverseTermM f (x, y) = (,) <$> traverseTermM f x <*> traverseTermM f y
  foldTerm f (x, y) = foldTerm f x `mappend` foldTerm f y

instance (TermLike a, TermLike b, TermLike c) => TermLike (a, b, c) where
  traverseTermM f (x, y, z) = (,,) <$> traverseTermM f x <*> traverseTermM f y <*> traverseTermM f z
  foldTerm f (x, y, z) = mconcat [foldTerm f x, foldTerm f y, foldTerm f z]

instance (TermLike a, TermLike b, TermLike c, TermLike d) => TermLike (a, b, c, d) where
  traverseTermM f (x, y, z, u) = (,,,) <$> traverseTermM f x <*> traverseTermM f y <*> traverseTermM f z <*> traverseTermM f u
  foldTerm f (x, y, z, u) = mconcat [foldTerm f x, foldTerm f y, foldTerm f z, foldTerm f u]

-- Real terms

instance TermLike Term where

  traverseTermM f t = case t of
    Var i xs    -> f =<< Var i <$> traverseTermM f xs
    Def c xs    -> f =<< Def c <$> traverseTermM f xs
    Con c ci xs -> f =<< Con c ci <$> traverseTermM f xs
    Lam h b     -> f =<< Lam h <$> traverseTermM f b
    Pi a b      -> f =<< uncurry Pi <$> traverseTermM f (a, b)
    MetaV m xs  -> f =<< MetaV m <$> traverseTermM f xs
    Level l     -> f =<< Level <$> traverseTermM f l
    Lit _       -> f t
    Sort s      -> f =<< Sort <$> traverseTermM f s
    DontCare mv -> f =<< DontCare <$> traverseTermM f mv
    Dummy{}     -> f t

  foldTerm f t = f t `mappend` case t of
    Var i xs    -> foldTerm f xs
    Def c xs    -> foldTerm f xs
    Con c ci xs -> foldTerm f xs
    Lam h b     -> foldTerm f b
    Pi a b      -> foldTerm f (a, b)
    MetaV m xs  -> foldTerm f xs
    Level l     -> foldTerm f l
    Lit _       -> mempty
    Sort s      -> foldTerm f s
    DontCare mv -> foldTerm f mv
    Dummy{}     -> mempty

instance TermLike Level where
  traverseTermM f (Max n as) = Max n <$> traverseTermM f as
  foldTerm f      (Max n as) = foldTerm f as

instance TermLike PlusLevel where
  traverseTermM f (Plus n l) = Plus n <$> traverseTermM f l
  foldTerm f (Plus _ l)      = foldTerm f l

instance TermLike LevelAtom where
  traverseTermM f l = case l of
    MetaLevel m vs   -> MetaLevel m <$> traverseTermM f vs
    NeutralLevel r v -> NeutralLevel r <$> traverseTermM f v
    BlockedLevel m v -> BlockedLevel m <$> traverseTermM f v
    UnreducedLevel v -> UnreducedLevel <$> traverseTermM f v
  foldTerm f l = case l of
    MetaLevel m vs   -> foldTerm f vs
    NeutralLevel _ v -> foldTerm f v
    BlockedLevel _ v -> foldTerm f v
    UnreducedLevel v -> foldTerm f v

instance TermLike Type where
  traverseTermM f (El s t) = El s <$> traverseTermM f t
  foldTerm f (El s t) = foldTerm f t

instance TermLike Sort where
  traverseTermM f s = case s of
    Type l     -> Type <$> traverseTermM f l
    Prop l     -> Prop <$> traverseTermM f l
    Inf        -> pure s
    SizeUniv   -> pure s
    PiSort a b -> PiSort   <$> traverseTermM f a <*> traverseTermM f b
    UnivSort a -> UnivSort <$> traverseTermM f a
    MetaS x es -> MetaS x  <$> traverseTermM f es
    DefS q es  -> DefS q   <$> traverseTermM f es
    DummyS{}   -> pure s

  foldTerm f s = case s of
    Type l     -> foldTerm f l
    Prop l     -> foldTerm f l
    Inf        -> mempty
    SizeUniv   -> mempty
    PiSort a b -> foldTerm f a <> foldTerm f b
    UnivSort a -> foldTerm f a
    MetaS _ es -> foldTerm f es
    DefS _ es  -> foldTerm f es
    DummyS{}   -> mempty

instance TermLike EqualityView where

  traverseTermM f v = case v of
    OtherType t -> OtherType
      <$> traverseTermM f t
    EqualityType s eq l t a b -> EqualityType s eq
      <$> traverse (traverseTermM f) l
      <*> traverseTermM f t
      <*> traverseTermM f a
      <*> traverseTermM f b

  foldTerm f v = case v of
    OtherType t -> foldTerm f t
    EqualityType s eq l t a b -> foldTerm f (l ++ [t, a, b])

-- | Put it in a monad to make it possible to do strictly.
copyTerm :: (TermLike a, Monad m) => a -> m a
copyTerm = traverseTermM return
