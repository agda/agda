
-- | Tools for patterns in concrete syntax.

module Agda.Syntax.Concrete.Pattern where

import Control.Applicative ( liftA2 )
import Control.Arrow ( first )
import Control.Monad ( (>=>) )
import Control.Monad.Identity

import Data.Monoid ( Any(..), Endo(..), Sum(..) )

import Agda.Syntax.Common
import Agda.Syntax.Concrete

import Agda.Utils.AffineHole
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.List1  ( List1, pattern (:|) )
import Agda.Utils.List2  ( List2 )
import Agda.Utils.Maybe
import Agda.Utils.Singleton
import qualified Agda.Utils.List1 as List1


-- | Check for ellipsis @...@.

class IsEllipsis a where
  isEllipsis :: a -> Bool

-- | Is the pattern just @...@?
instance IsEllipsis Pattern where
  isEllipsis = \case
    EllipsisP{}         -> True
    ParenP _ p          -> isEllipsis p
    _ -> False

-- | Has the lhs an occurrence of the ellipsis @...@?

class HasEllipsis a where
  hasEllipsis :: a -> Bool

instance HasEllipsis Pattern where
  hasEllipsis p =
    case hasEllipsis' p of
      ZeroHoles _ -> False
      OneHole _ _ -> True
      ManyHoles   -> True

-- | Does the lhs contain an ellipsis?
instance HasEllipsis LHS where
  hasEllipsis (LHS p _ _) = hasEllipsis p
  -- clauses that are already expanded don't have an ellipsis

-- | Check for with-pattern @| p@.

class IsWithP p where
  isWithP :: p -> Maybe p

  default isWithP :: (IsWithP q, Decoration f, f q ~ p) => p -> Maybe p
  isWithP = traverseF isWithP

instance IsWithP Pattern where
  isWithP = \case
    WithP _ p           -> Just p
    ParenP _ p          -> isWithP p
    _ -> Nothing

instance IsWithP p => IsWithP (Arg p) where
instance IsWithP p => IsWithP (Named n p) where


-- * LHS manipulation (see also ''Agda.Syntax.Abstract.Pattern'')

-- | The next patterns are ...
--
-- (This view discards 'PatInfo'.)
data LHSPatternView
  = LHSAppP  [NamedArg Pattern]
      -- ^ Application patterns (non-empty list).
  | LHSWithP [Pattern]
      -- ^ With patterns (non-empty list).
      --   These patterns are not prefixed with 'WithP'.

-- | Construct the 'LHSPatternView' of the given list (if not empty).
--
-- Return the view and the remaining patterns.

lhsPatternView :: [NamedArg Pattern] -> Maybe (LHSPatternView, [NamedArg Pattern])
lhsPatternView [] = Nothing
lhsPatternView (p0 : ps) =
  case namedArg p0 of
    WithP _i p   -> Just (LHSWithP (p : map namedArg ps1), ps2)
      where
      (ps1, ps2) = spanJust isWithP ps
    -- If the next pattern is an application pattern, collect more of these
    _ -> Just (LHSAppP (p0 : ps1), ps2)
      where
      (ps1, ps2) = span (isNothing . isWithP) ps

-- | Add applicative patterns (non-projection / non-with patterns) to the right.
lhsCoreApp :: LHSCore -> [NamedArg Pattern] -> LHSCore
lhsCoreApp core ps = core { lhsPats = lhsPats core ++ ps }

-- | Add with-patterns to the right.
lhsCoreWith :: LHSCore -> [Pattern] -> LHSCore
lhsCoreWith (LHSWith core wps []) wps' = LHSWith core (wps ++ wps') []
lhsCoreWith core                  wps' = LHSWith core wps' []

-- | Append patterns to 'LHSCore', separating with patterns from the rest.
lhsCoreAddSpine :: LHSCore -> [NamedArg Pattern] -> LHSCore
lhsCoreAddSpine core ps0 =
  -- Recurse on lhsPatternView until no patterns left.
  case lhsPatternView ps0 of
    Nothing       -> core
    Just (LHSAppP  ps , ps') -> lhsCoreApp  core ps  `lhsCoreAddSpine` ps'
    Just (LHSWithP wps, ps') -> lhsCoreWith core wps `lhsCoreAddSpine` ps'


-- | Modify the 'Pattern' component in 'LHS'.
mapLhsOriginalPattern :: (Pattern -> Pattern) -> LHS -> LHS
mapLhsOriginalPattern f lhs@LHS{ lhsOriginalPattern = p } =
  lhs { lhsOriginalPattern = f p }

-- | Effectfully modify the 'Pattern' component in 'LHS'.
mapLhsOriginalPatternM :: (Functor m, Applicative m) => (Pattern -> m Pattern) -> LHS -> m LHS
mapLhsOriginalPatternM f lhs@LHS{ lhsOriginalPattern = p } = f p <&> \ p' ->
  lhs { lhsOriginalPattern = p' }

-- | Does the LHS contain projection patterns?
hasCopatterns :: LHSCore -> Bool
hasCopatterns = \case
  LHSHead{}     -> False
  LHSProj{}     -> True
  LHSWith h _ _ -> hasCopatterns h
  LHSEllipsis{} -> False

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

  -- | Traverse pattern with option of post-traversal modification.
  traverseCPatternA :: (Applicative m, Functor m)
      => (Pattern -> m Pattern -> m Pattern)
         -- ^ Combine a pattern and the its recursively computed version.
      -> p -> m p

  default traverseCPatternA :: (Traversable f, CPatternLike q, f q ~ p, Applicative m, Functor m)
      => (Pattern -> m Pattern -> m Pattern)
      -> p -> m p
  traverseCPatternA = traverse . traverseCPatternA

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
      RawAppP _ ps    -> foldrCPattern f ps
      OpAppP _ _ _ ps -> foldrCPattern f ps
      HiddenP _ ps    -> foldrCPattern f ps
      InstanceP _ ps  -> foldrCPattern f ps
      ParenP _ p      -> foldrCPattern f p
      AsP _ _ p       -> foldrCPattern f p
      WithP _ p       -> foldrCPattern f p
      RecP _ ps       -> foldrCPattern f ps
      EllipsisP _ mp  -> foldrCPattern f mp
      -- Nonrecursive cases:
      IdentP _        -> mempty
      WildP _         -> mempty
      DotP _ _        -> mempty
      AbsurdP _       -> mempty
      LitP _ _        -> mempty
      QuoteP _        -> mempty
      EqualP _ _      -> mempty

  traverseCPatternA f p0 = f p0 $ case p0 of
      -- Recursive cases:
      AppP        p ps    -> liftA2 AppP (traverseCPatternA f p) (traverseCPatternA f ps)
      RawAppP   r ps      -> RawAppP r     <$> traverseCPatternA f ps
      OpAppP    r x xs ps -> OpAppP r x xs <$> traverseCPatternA f ps
      HiddenP   r p       -> HiddenP r     <$> traverseCPatternA f p
      InstanceP r p       -> InstanceP r   <$> traverseCPatternA f p
      ParenP    r p       -> ParenP r      <$> traverseCPatternA f p
      AsP       r x p     -> AsP r x       <$> traverseCPatternA f p
      WithP     r p       -> WithP r       <$> traverseCPatternA f p
      RecP      r ps      -> RecP r        <$> traverseCPatternA f ps
      EllipsisP r mp      -> EllipsisP r   <$> traverseCPatternA f mp
      -- Nonrecursive cases:
      IdentP _        -> pure p0
      WildP _         -> pure p0
      DotP _ _        -> pure p0
      AbsurdP _       -> pure p0
      LitP _ _        -> pure p0
      QuoteP _        -> pure p0
      EqualP _ _      -> pure p0

  traverseCPatternM pre post = pre >=> recurse >=> post
    where
    recurse p0 = case p0 of
      -- Recursive cases:
      AppP        p ps    -> uncurry AppP  <$> traverseCPatternM pre post (p, ps)
      RawAppP   r ps      -> RawAppP r     <$> traverseCPatternM pre post ps
      OpAppP    r x xs ps -> OpAppP r x xs <$> traverseCPatternM pre post ps
      HiddenP   r p       -> HiddenP r     <$> traverseCPatternM pre post p
      InstanceP r p       -> InstanceP r   <$> traverseCPatternM pre post p
      ParenP    r p       -> ParenP r      <$> traverseCPatternM pre post p
      AsP       r x p     -> AsP r x       <$> traverseCPatternM pre post p
      WithP     r p       -> WithP r       <$> traverseCPatternM pre post p
      RecP      r ps      -> RecP r        <$> traverseCPatternM pre post ps
      EllipsisP r mp      -> EllipsisP r   <$> traverseCPatternM pre post mp
      -- Nonrecursive cases:
      IdentP _        -> return p0
      WildP _         -> return p0
      DotP _ _        -> return p0
      AbsurdP _       -> return p0
      LitP _ _        -> return p0
      QuoteP _        -> return p0
      EqualP _ _      -> return p0

instance (CPatternLike a, CPatternLike b) => CPatternLike (a,b) where
  foldrCPattern f (p, p') =
    foldrCPattern f p `mappend` foldrCPattern f p'

  traverseCPatternA f (p, p') =
    liftA2 (,)
      (traverseCPatternA f p)
      (traverseCPatternA f p')

  traverseCPatternM pre post (p, p') =
    liftA2 (,)
      (traverseCPatternM pre post p)
      (traverseCPatternM pre post p')

instance CPatternLike p => CPatternLike (Arg p)
instance CPatternLike p => CPatternLike (Named n p)
instance CPatternLike p => CPatternLike [p]
instance CPatternLike p => CPatternLike (List1 p)
instance CPatternLike p => CPatternLike (List2 p)
instance CPatternLike p => CPatternLike (Maybe p)
instance CPatternLike p => CPatternLike (FieldAssignment' p)

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
    WithP _ _      -> mempty
    RawAppP _ _    -> mempty
    HiddenP _ _    -> mempty
    ParenP _ _     -> mempty
    WildP _        -> mempty
    AbsurdP _      -> mempty
    DotP _ _       -> mempty
    LitP _ _       -> mempty
    QuoteP _       -> mempty
    InstanceP _ _  -> mempty
    RecP _ _       -> mempty
    EqualP _ _     -> mempty
    EllipsisP _ _  -> mempty

-- | Get all the identifiers in a pattern in left-to-right order.
patternNames :: Pattern -> [Name]
patternNames = map unqualify . patternQNames

-- | Does the pattern contain a with-pattern?
-- (Shortcutting.)
hasWithPatterns :: CPatternLike p => p -> Bool
hasWithPatterns = getAny . foldCPattern (Any . isWithPattern)

-- | Is 'WithP'?
isWithPattern :: Pattern -> Bool
isWithPattern = \case
  WithP{} -> True
  _ -> False

-- | Count the number of with-subpatterns in a pattern?
numberOfWithPatterns :: CPatternLike p => p -> Int
numberOfWithPatterns = getSum . foldCPattern (Sum . f)
  where f p = if isWithPattern p then 1 else 0

-- | Compute the context in which the ellipsis occurs, if at all.
--   If there are several occurrences, this is an error.
--   This only counts ellipsis that haven't already been expanded.
hasEllipsis' :: CPatternLike p => p -> AffineHole Pattern p
hasEllipsis' = traverseCPatternA $ \ p mp ->
  case p of
    EllipsisP _ Nothing -> OneHole id p
    _                   -> mp

reintroduceEllipsis :: ExpandedEllipsis -> Pattern -> Pattern
reintroduceEllipsis (ExpandedEllipsis r k) p | hasWithPatterns p =
  let (args, wargs) = splitEllipsis k $ List1.toList $ patternAppView p
      (hd,args') = fromMaybe __IMPOSSIBLE__ $ uncons args
      core = foldl AppP (namedArg hd) args
  in foldl AppP (EllipsisP r $ Just $ core) wargs
reintroduceEllipsis _ p = p

splitEllipsis :: (IsWithP p) => Int -> [p] -> ([p],[p])
splitEllipsis k [] = ([] , [])
splitEllipsis k (p:ps)
  | isJust (isWithP p) = if
      | k == 0    -> ([] , p:ps)
      | otherwise -> first (p:) $ splitEllipsis (k-1) ps
  | otherwise = first (p:) $ splitEllipsis k ps

---------------------------------------------------------------------------
-- * Helpers for pattern and lhs parsing
---------------------------------------------------------------------------

-- | View a pattern @p@ as a list @p0 .. pn@ where @p0@ is the identifier
--   (in most cases a constructor).
--
--  Pattern needs to be parsed already (operators resolved).
patternAppView :: Pattern -> List1 (NamedArg Pattern)
patternAppView = \case
    AppP p arg      -> patternAppView p `List1.appendList` [arg]
    OpAppP _ x _ ps -> defaultNamedArg (IdentP x) :| ps
    ParenP _ p      -> patternAppView p
    RawAppP _ _     -> __IMPOSSIBLE__
    p               -> singleton $ defaultNamedArg p
