{-# LANGUAGE CPP          #-}
{-# LANGUAGE TypeFamilies #-}  -- For type equality.

-- | Tools for patterns in concrete syntax.

module Agda.Syntax.Concrete.Pattern where

import Control.Applicative ( liftA2 )
import Control.Monad.Identity

import Data.Foldable    (Foldable, foldMap)
import Data.Traversable (Traversable, traverse)
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Concrete

import Agda.Utils.Functor


-- | Check for ellipsis @...@.

class IsEllipsis a where
  isEllipsis :: a -> Bool

-- | Is the pattern just @...@?
instance IsEllipsis Pattern where
  isEllipsis = \case
    EllipsisP{}   -> True
    RawAppP _ [p] -> isEllipsis p
    ParenP _ p    -> isEllipsis p
    _ -> False

-- | Does the lhs contain an ellipsis?
instance IsEllipsis LHS where
  isEllipsis (LHS p _ _ _) = isEllipsis p


-- | Modify the 'Pattern' component in 'LHS'.
mapLhsOriginalPattern :: (Pattern -> Pattern) -> LHS -> LHS
mapLhsOriginalPattern f lhs@LHS{ lhsOriginalPattern = p } =
  lhs { lhsOriginalPattern = f p }

-- | Effectfully modify the 'Pattern' component in 'LHS'.
mapLhsOriginalPatternM :: (Functor m, Applicative m) => (Pattern -> m Pattern) -> LHS -> m LHS
mapLhsOriginalPatternM f lhs@LHS{ lhsOriginalPattern = p } = f p <&> \ p' ->
  lhs { lhsOriginalPattern = p' }


-- * Generic fold

-- | Generic pattern traversal.
--
-- See 'Agda.Syntax.Abstract.Pattern.APatternLike'.

class CPatternLike p where

  -- | Fold pattern.
  foldrCPattern
    :: Monoid m
    => (Pattern -> m -> m)
         -- ^ Combine a pattern and the value computed from its subpatterns.
    -> p -> m

  default foldrCPattern
    :: (Monoid m, Foldable f, CPatternLike q, f q ~ p)
    => (Pattern -> m -> m) -> p -> m
  foldrCPattern = foldMap . foldrCPattern

  -- | Traverse pattern.
  traverseCPatternM
    :: Monad m => (Pattern -> m Pattern)  -- ^ @pre@: Modification before recursion.
    -> (Pattern -> m Pattern)  -- ^ @post@: Modification after recursion.
    -> p -> m p

  default traverseCPatternM
    :: (Traversable f, CPatternLike q, f q ~ p, Monad m)
    => (Pattern -> m Pattern)
    -> (Pattern -> m Pattern)
    -> p -> m p
  traverseCPatternM pre post = traverse $ traverseCPatternM pre post

instance CPatternLike Pattern where
  foldrCPattern f p0 = f p0 $
    case p0 of
      -- Recursive cases:
      AppP p ps       -> foldrCPattern f (p, ps)
      WithAppP _ p ps -> foldrCPattern f (p, ps)
      RawAppP _ ps    -> foldrCPattern f ps
      OpAppP _ _ _ ps -> foldrCPattern f ps
      HiddenP _ ps    -> foldrCPattern f ps
      InstanceP _ ps  -> foldrCPattern f ps
      ParenP _ p      -> foldrCPattern f p
      AsP _ _ p       -> foldrCPattern f p
      RecP _ ps       -> foldrCPattern f ps
      -- Nonrecursive cases:
      IdentP _        -> mempty
      WildP _         -> mempty
      DotP _ _ _      -> mempty
      AbsurdP _       -> mempty
      LitP _          -> mempty
      QuoteP _        -> mempty
      EqualP _ _      -> mempty
      EllipsisP _     -> mempty

  traverseCPatternM pre post = pre >=> recurse >=> post
    where
    recurse p0 = case p0 of
      -- Recursive cases:
      AppP        p ps    -> uncurry AppP         <$> traverseCPatternM pre post (p, ps)
      WithAppP  r p ps    -> uncurry (WithAppP r) <$> traverseCPatternM pre post (p, ps)
      RawAppP   r ps      -> RawAppP r            <$> traverseCPatternM pre post ps
      OpAppP    r x xs ps -> OpAppP r x xs        <$> traverseCPatternM pre post ps
      HiddenP   r p       -> HiddenP r            <$> traverseCPatternM pre post p
      InstanceP r p       -> InstanceP r          <$> traverseCPatternM pre post p
      ParenP    r p       -> ParenP r             <$> traverseCPatternM pre post p
      AsP       r x p     -> AsP r x              <$> traverseCPatternM pre post p
      RecP      r ps      -> RecP r               <$> traverseCPatternM pre post ps
      -- Nonrecursive cases:
      IdentP _        -> return p0
      WildP _         -> return p0
      DotP _ _ _      -> return p0
      AbsurdP _       -> return p0
      LitP _          -> return p0
      QuoteP _        -> return p0
      EqualP _ _      -> return p0
      EllipsisP _     -> return p0

instance (CPatternLike a, CPatternLike b) => CPatternLike (a,b) where
  foldrCPattern f (p, p') =
    foldrCPattern f p `mappend` foldrCPattern f p'

  traverseCPatternM pre post (p, p') =
    liftA2 (,)
      (traverseCPatternM pre post p)
      (traverseCPatternM pre post p')

instance CPatternLike p => CPatternLike (Arg p)              where
instance CPatternLike p => CPatternLike (Named n p)          where
instance CPatternLike p => CPatternLike [p]                  where
instance CPatternLike p => CPatternLike (Maybe p)            where
instance CPatternLike p => CPatternLike (FieldAssignment' p) where

-- | Compute a value from each subpattern and collect all values in a monoid.

foldCPattern :: (CPatternLike p, Monoid m) => (Pattern -> m) -> p -> m
foldCPattern f = foldrCPattern $ \ p m -> f p `mappend` m

-- | Traverse pattern(s) with a modification before the recursive descent.

preTraverseCPatternM
  :: (CPatternLike p, Monad m)
  => (Pattern -> m Pattern)  -- ^ @pre@: Modification before recursion.
  -> p -> m p
preTraverseCPatternM pre p = traverseCPatternM pre return p

-- | Traverse pattern(s) with a modification after the recursive descent.

postTraverseCPatternM
  :: (CPatternLike p, Monad m)
  => (Pattern -> m Pattern)  -- ^ @post@: Modification after recursion.
  -> p -> m p
postTraverseCPatternM post p = traverseCPatternM return post p

-- | Map pattern(s) with a modification after the recursive descent.

mapCPattern :: CPatternLike p => (Pattern -> Pattern) -> p -> p
mapCPattern f = runIdentity . postTraverseCPatternM (Identity . f)


-- * Specific folds.

-- | Get all the identifiers in a pattern in left-to-right order.
--
-- Implemented using difference lists.
patternQNames :: CPatternLike p => p -> [QName]
patternQNames p = foldCPattern f p `appEndo` []
  where
  f :: Pattern -> Endo [QName]
  f = \case
    IdentP x       -> Endo (x :)
    OpAppP _ x _ _ -> Endo (x :)
    AsP _ x _      -> mempty  -- x must be a bound name, can't be a constructor!
    AppP _ _       -> mempty
    WithAppP _ _ _ -> mempty
    RawAppP _ _    -> mempty
    HiddenP _ _    -> mempty
    ParenP _ _     -> mempty
    WildP _        -> mempty
    AbsurdP _      -> mempty
    DotP _ _ _     -> mempty
    LitP _         -> mempty
    QuoteP _       -> mempty
    InstanceP _ _  -> mempty
    RecP _ _       -> mempty
    EqualP _ _     -> mempty
    EllipsisP _    -> mempty

-- | Get all the identifiers in a pattern in left-to-right order.
patternNames :: Pattern -> [Name]
patternNames = map unqualify . patternQNames
