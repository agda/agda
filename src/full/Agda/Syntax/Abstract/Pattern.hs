
-- | Auxiliary functions to handle patterns in the abstract syntax.
--
--   Generic and specific traversals.

module Agda.Syntax.Abstract.Pattern where

import Prelude hiding (null)

import Control.Arrow           ( (***), second )
import Control.Monad           ( (>=>) )
import Control.Monad.Identity  ( Identity(..), runIdentity )
import Control.Applicative     ( liftA2 )


import Data.Maybe
import Data.Monoid

import Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment')
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pattern (IsWithP(..))
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Null

import Agda.Utils.Impossible

-- * Generic traversals
------------------------------------------------------------------------

type NAP = NamedArg Pattern

class MapNamedArgPattern a  where
  mapNamedArgPattern :: (NAP -> NAP) -> a -> a

  default mapNamedArgPattern
     :: (Functor f, MapNamedArgPattern a', a ~ f a') => (NAP -> NAP) -> a -> a
  mapNamedArgPattern = fmap . mapNamedArgPattern

instance MapNamedArgPattern NAP where
  mapNamedArgPattern f p =
    case namedArg p of
      -- no sub patterns:
      VarP{}    -> f p
      WildP{}   -> f p
      DotP{}    -> f p
      EqualP{}  -> f p
      LitP{}    -> f p
      AbsurdP{} -> f p
      ProjP{}   -> f p
      -- list of NamedArg subpatterns:
      ConP i qs ps       -> f $ setNamedArg p $ ConP i qs $ mapNamedArgPattern f ps
      DefP i qs ps       -> f $ setNamedArg p $ DefP i qs $ mapNamedArgPattern f ps
      PatternSynP i x ps -> f $ setNamedArg p $ PatternSynP i x $ mapNamedArgPattern f ps
      -- Pattern subpattern(s):
      -- RecP: we copy the NamedArg info to the subpatterns but discard it after recursion
      RecP i fs          -> f $ setNamedArg p $ RecP i $ map (fmap namedArg) $ mapNamedArgPattern f $ map (fmap (setNamedArg p)) fs
      -- AsP: we hand the NamedArg info to the subpattern
      AsP i x p0         -> f $ updateNamedArg (AsP i x) $ mapNamedArgPattern f $ setNamedArg p p0
      -- WithP: like AsP
      WithP i p0         -> f $ updateNamedArg (WithP i) $ mapNamedArgPattern f $ setNamedArg p p0
      AnnP i a p0        -> f $ updateNamedArg (AnnP i a) $ mapNamedArgPattern f $ setNamedArg p p0

instance MapNamedArgPattern a => MapNamedArgPattern [a]                  where
instance MapNamedArgPattern a => MapNamedArgPattern (FieldAssignment' a) where
instance MapNamedArgPattern a => MapNamedArgPattern (Maybe a)            where

instance (MapNamedArgPattern a, MapNamedArgPattern b) => MapNamedArgPattern (a,b) where
  mapNamedArgPattern f (a, b) = (mapNamedArgPattern f a, mapNamedArgPattern f b)

-- | Generic pattern traversal.

class APatternLike p where
  type ADotT p

  -- | Fold pattern.
  foldrAPattern
    :: Monoid m
    => (Pattern' (ADotT p) -> m -> m)
         -- ^ Combine a pattern and the value computed from its subpatterns.
    -> p -> m

  default foldrAPattern
    :: (Monoid m, Foldable f, APatternLike b, (ADotT p) ~ (ADotT b), f b ~ p)
    => (Pattern' (ADotT p) -> m -> m) -> p -> m
  foldrAPattern = foldMap . foldrAPattern

  -- | Traverse pattern.
  traverseAPatternM
    :: Monad m
    => (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))  -- ^ @pre@: Modification before recursion.
    -> (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))  -- ^ @post@: Modification after recursion.
    -> p -> m p

  default traverseAPatternM
    :: (Traversable f, APatternLike q, (ADotT p) ~ (ADotT q), f q ~ p, Monad m)
    => (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))
    -> (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))
    -> p -> m p
  traverseAPatternM pre post = traverse $ traverseAPatternM pre post

-- | Compute from each subpattern a value and collect them all in a monoid.

foldAPattern :: (APatternLike p, Monoid m) => (Pattern' (ADotT p) -> m) -> p -> m
foldAPattern f = foldrAPattern $ \ p m -> f p `mappend` m

-- | Traverse pattern(s) with a modification before the recursive descent.

preTraverseAPatternM
  :: (APatternLike p, Monad m )
  => (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))  -- ^ @pre@: Modification before recursion.
  -> p -> m p
preTraverseAPatternM pre p = traverseAPatternM pre return p

-- | Traverse pattern(s) with a modification after the recursive descent.

postTraverseAPatternM
  :: (APatternLike p, Monad m )
  => (Pattern' (ADotT p) -> m (Pattern' (ADotT p)))  -- ^ @post@: Modification after recursion.
  -> p -> m p
postTraverseAPatternM post p = traverseAPatternM return post p

-- | Map pattern(s) with a modification after the recursive descent.

mapAPattern :: APatternLike p => (Pattern' (ADotT p) -> Pattern' (ADotT p)) -> p -> p
mapAPattern f = runIdentity . postTraverseAPatternM (Identity . f)

-- Interesting instance:

instance APatternLike (Pattern' a) where
  type ADotT (Pattern' a) = a

  foldrAPattern f p = f p $
    case p of
      AsP _ _ p          -> foldrAPattern f p
      ConP _ _ ps        -> foldrAPattern f ps
      DefP _ _ ps        -> foldrAPattern f ps
      RecP _ ps          -> foldrAPattern f ps
      PatternSynP _ _ ps -> foldrAPattern f ps
      WithP _ p          -> foldrAPattern f p
      VarP _             -> mempty
      ProjP _ _ _        -> mempty
      WildP _            -> mempty
      DotP _ _           -> mempty
      AbsurdP _          -> mempty
      LitP _ _           -> mempty
      EqualP _ _         -> mempty
      AnnP _ _ p         -> foldrAPattern f p

  traverseAPatternM pre post = pre >=> recurse >=> post
    where
    recurse = \case
      -- Non-recursive cases:
      p@A.VarP{}            -> return p
      p@A.WildP{}           -> return p
      p@A.DotP{}            -> return p
      p@A.LitP{}            -> return p
      p@A.AbsurdP{}         -> return p
      p@A.ProjP{}           -> return p
      p@A.EqualP{}          -> return p
      -- Recursive cases:
      A.ConP        i ds ps -> A.ConP        i ds <$> traverseAPatternM pre post ps
      A.DefP        i q  ps -> A.DefP        i q  <$> traverseAPatternM pre post ps
      A.AsP         i x  p  -> A.AsP         i x  <$> traverseAPatternM pre post p
      A.RecP        i    ps -> A.RecP        i    <$> traverseAPatternM pre post ps
      A.PatternSynP i x  ps -> A.PatternSynP i x  <$> traverseAPatternM pre post ps
      A.WithP       i p     -> A.WithP       i    <$> traverseAPatternM pre post p
      A.AnnP        i a  p  -> A.AnnP        i a  <$> traverseAPatternM pre post p

instance APatternLike a => APatternLike (Arg a) where
  type ADotT (Arg a) = ADotT a

instance APatternLike a => APatternLike (Named n a) where
  type ADotT (Named n a) = ADotT a

instance APatternLike a => APatternLike [a] where
  type ADotT [a] = ADotT a

instance APatternLike a => APatternLike (Maybe a) where
  type ADotT (Maybe a) = ADotT a

instance APatternLike a => APatternLike (FieldAssignment' a) where
  type ADotT (FieldAssignment' a) = ADotT a

instance (APatternLike a, APatternLike b, ADotT a ~ ADotT b) => APatternLike (a, b) where
  type ADotT (a, b) = ADotT a

  foldrAPattern f (p, p') =
    foldrAPattern f p `mappend` foldrAPattern f p'

  traverseAPatternM pre post (p, p') =
    liftA2 (,)
      (traverseAPatternM pre post p)
      (traverseAPatternM pre post p')


-- * Specific folds
------------------------------------------------------------------------

-- | Collect pattern variables in left-to-right textual order.

patternVars :: APatternLike p => p -> [A.Name]
patternVars p = foldAPattern f p `appEndo` []
  where
  -- We use difference lists @[A.Name] -> [A.Name]@ to avoid reconcatenation.
  f :: Pattern' a -> Endo [A.Name]
  f = \case
    A.VarP x         -> Endo (unBind x :)
    A.AsP _ x _      -> Endo (unBind x :)
    A.LitP        {} -> mempty
    A.ConP        {} -> mempty
    A.RecP        {} -> mempty
    A.DefP        {} -> mempty
    A.ProjP       {} -> mempty
    A.WildP       {} -> mempty
    A.DotP        {} -> mempty
    A.AbsurdP     {} -> mempty
    A.EqualP      {} -> mempty
    A.PatternSynP {} -> mempty
    A.WithP _ _      -> mempty
    A.AnnP        {} -> mempty

-- | Check if a pattern contains a specific (sub)pattern.

containsAPattern :: APatternLike p => (Pattern' (ADotT p) -> Bool) -> p -> Bool
containsAPattern f = getAny . foldAPattern (Any . f)

-- | Check if a pattern contains an absurd pattern.
--   For instance, @suc ()@, does so.
--
--   Precondition: contains no pattern synonyms.

containsAbsurdPattern :: APatternLike p => p -> Bool
containsAbsurdPattern = containsAPattern $ \case
    A.PatternSynP{} -> __IMPOSSIBLE__
    A.AbsurdP{}     -> True
    _               -> False

-- | Check if a pattern contains an @-pattern.
--
containsAsPattern :: APatternLike p => p -> Bool
containsAsPattern = containsAPattern $ \case
    A.AsP{}         -> True
    _               -> False

-- | Check if any user-written pattern variables occur more than once,
--   and throw the given error if they do.
checkPatternLinearity :: (Monad m, APatternLike p)
                      => p -> ([C.Name] -> m ()) -> m ()
checkPatternLinearity ps err =
  unlessNull (duplicates $ map nameConcrete $ patternVars ps) $ \ys -> err ys


-- * Specific traversals
------------------------------------------------------------------------

-- | Pattern substitution.
--
-- For the embedded expression, the given pattern substitution is turned into
-- an expression substitution.

substPattern :: [(Name, Pattern)] -> Pattern -> Pattern
substPattern s = substPattern' (substExpr $ map (second patternToExpr) s) s

-- | Pattern substitution, parametrized by substitution function for embedded expressions.

substPattern'
  :: (e -> e)              -- ^ Substitution function for expressions.
  -> [(Name, Pattern' e)]  -- ^ (Parallel) substitution.
  -> Pattern' e            -- ^ Input pattern.
  -> Pattern' e
substPattern' subE s = mapAPattern $ \ p -> case p of
  VarP x            -> fromMaybe p $ lookup (A.unBind x) s
  DotP i e          -> DotP i $ subE e
  EqualP i es       -> EqualP i $ map (subE *** subE) es
  AnnP i a p        -> AnnP i (subE a) p
  -- No action on the other patterns (besides the recursion):
  ConP _ _ _        -> p
  RecP _ _          -> p
  ProjP _ _ _       -> p
  WildP _           -> p
  AbsurdP _         -> p
  LitP _ _          -> p
  DefP _ _ _        -> p
  AsP _ _ _         -> p -- Note: cannot substitute into as-variable
  PatternSynP _ _ _ -> p
  WithP _ _         -> p


-- * Other pattern utilities
------------------------------------------------------------------------

-- | Check for with-pattern.
instance IsWithP (Pattern' e) where
  isWithP = \case
    WithP _ p -> Just p
    _ -> Nothing

-- | Split patterns into (patterns, trailing with-patterns).
splitOffTrailingWithPatterns :: A.Patterns -> (A.Patterns, A.Patterns)
splitOffTrailingWithPatterns = spanEnd (isJust . isWithP)

-- | Get the tail of with-patterns of a pattern spine.
trailingWithPatterns :: Patterns -> Patterns
trailingWithPatterns = snd . splitOffTrailingWithPatterns

-- | The next patterns are ...
--
-- (This view discards 'PatInfo'.)
data LHSPatternView e
  = LHSAppP  (NAPs e)
      -- ^ Application patterns (non-empty list).
  | LHSProjP ProjOrigin AmbiguousQName (NamedArg (Pattern' e))
      -- ^ A projection pattern.  Is also stored unmodified here.
  | LHSWithP [Pattern' e]
      -- ^ With patterns (non-empty list).
      --   These patterns are not prefixed with 'WithP'.
  deriving (Show)

-- | Construct the 'LHSPatternView' of the given list (if not empty).
--
-- Return the view and the remaining patterns.

lhsPatternView :: IsProjP e => NAPs e -> Maybe (LHSPatternView e, NAPs e)
lhsPatternView [] = Nothing
lhsPatternView (p0 : ps) =
  case namedArg p0 of
    ProjP _i o d -> Just (LHSProjP o d p0, ps)
    -- If the next pattern is a with-pattern, collect more with-patterns
    WithP _i p   -> Just (LHSWithP (p : map namedArg ps1), ps2)
      where
      (ps1, ps2) = spanJust isWithP ps
    -- If the next pattern is an application pattern, collect more of these
    _ -> Just (LHSAppP (p0 : ps1), ps2)
      where
      (ps1, ps2) = span (\ p -> isNothing (isProjP p) && isNothing (isWithP p)) ps

-- * Left-hand-side manipulation
------------------------------------------------------------------------

-- | Convert a focused lhs to spine view and back.
class LHSToSpine a b where
  lhsToSpine :: a -> b
  spineToLhs :: b -> a

-- | Clause instance.
instance LHSToSpine Clause SpineClause where
  lhsToSpine = fmap lhsToSpine
  spineToLhs = fmap spineToLhs

-- | List instance (for clauses).
instance LHSToSpine a b => LHSToSpine [a] [b] where
  lhsToSpine = map lhsToSpine
  spineToLhs = map spineToLhs

-- | LHS instance.
instance LHSToSpine LHS SpineLHS where
  lhsToSpine (LHS i core) = SpineLHS i f ps
    where QNamed f ps = lhsCoreToSpine core
  spineToLhs (SpineLHS i f ps) = LHS i (spineToLhsCore $ QNamed f ps)

lhsCoreToSpine :: LHSCore' e -> A.QNamed [NamedArg (Pattern' e)]
lhsCoreToSpine = \case
  LHSHead f ps     -> QNamed f ps
  LHSProj d h ps   -> lhsCoreToSpine (namedArg h) <&> (++ (p : ps))
    where p = updateNamedArg (const $ ProjP empty ProjPrefix d) h
  LHSWith h wps ps -> lhsCoreToSpine h <&> (++ map fromWithPat wps ++ ps)
    where
      fromWithPat :: Arg (Pattern' e) -> NamedArg (Pattern' e)
      fromWithPat = fmap (unnamed . mkWithP)
      mkWithP p   = WithP (PatRange $ getRange p) p

spineToLhsCore :: IsProjP e => QNamed [NamedArg (Pattern' e)] -> LHSCore' e
spineToLhsCore (QNamed f ps) = lhsCoreAddSpine (LHSHead f []) ps

-- | Add applicative patterns (non-projection / non-with patterns) to the right.
lhsCoreApp :: LHSCore' e -> [NamedArg (Pattern' e)] -> LHSCore' e
lhsCoreApp core ps = core { lhsPats = lhsPats core ++ ps }

-- | Add with-patterns to the right.
lhsCoreWith :: LHSCore' e -> [Arg (Pattern' e)] -> LHSCore' e
lhsCoreWith (LHSWith core wps []) wps' = LHSWith core (wps ++ wps') []
lhsCoreWith core                  wps' = LHSWith core wps' []

lhsCoreAddChunk :: IsProjP e => LHSCore' e -> LHSPatternView e -> LHSCore' e
lhsCoreAddChunk core = \case
  LHSAppP ps               -> lhsCoreApp core ps
  LHSWithP wps             -> lhsCoreWith core (defaultArg <$> wps)
  LHSProjP ProjPrefix d np -> LHSProj d (setNamedArg np core) []  -- Prefix projection pattern.
  LHSProjP _          _ np -> lhsCoreApp core [np]       -- Postfix projection pattern.

-- | Add projection, with, and applicative patterns to the right.
lhsCoreAddSpine :: IsProjP e => LHSCore' e -> [NamedArg (Pattern' e)] -> LHSCore' e
lhsCoreAddSpine core ps =
  -- Recurse on lhsPatternView until no patterns left.
  case lhsPatternView ps of
    Nothing       -> core
    Just (v, ps') -> lhsCoreAddChunk core chunk `lhsCoreAddSpine` ps'
      where
      -- Andreas, 2016-06-13
      -- If the projection was written prefix by the user
      -- or it is a fully applied operator
      -- we turn it to prefix projection form.
      chunk = case v of
        LHSProjP ProjPrefix _ _
          -> v
        LHSProjP _ d np | let nh = C.numHoles d, nh > 0, nh <= 1 + length ps'
          -> LHSProjP ProjPrefix d np
        _ -> v

-- | Used for checking pattern linearity.
lhsCoreAllPatterns :: LHSCore' e -> [Pattern' e]
lhsCoreAllPatterns = map namedArg . qnamed . lhsCoreToSpine

-- | Used in ''Agda.Syntax.Translation.AbstractToConcrete''.
--   Returns a 'DefP'.
lhsCoreToPattern :: LHSCore -> Pattern
lhsCoreToPattern lc =
  case lc of
    LHSHead f aps         -> DefP noInfo (unambiguous f) aps
    LHSProj d lhscore aps -> DefP noInfo d $
      fmap (fmap lhsCoreToPattern) lhscore : aps
    LHSWith h wps aps     -> case lhsCoreToPattern h of
      DefP r q ps         -> DefP r q $ ps ++ map fromWithPat wps ++ aps
        where
          fromWithPat :: Arg Pattern -> NamedArg Pattern
          fromWithPat = fmap (unnamed . mkWithP)
          mkWithP p   = WithP (PatRange $ getRange p) p
      _ -> __IMPOSSIBLE__
  where noInfo = empty -- TODO, preserve range!

mapLHSHead :: (QName -> [NamedArg Pattern] -> LHSCore) -> LHSCore -> LHSCore
mapLHSHead f = \case
  LHSHead x ps     -> f x ps
  LHSProj d h ps   -> LHSProj d (fmap (fmap (mapLHSHead f)) h) ps
  LHSWith h wps ps -> LHSWith (mapLHSHead f h) wps ps
