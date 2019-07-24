{-# LANGUAGE UndecidableInstances #-}

-- | A syntactic equality check that takes meta instantiations into account,
--   but does not reduce.  It replaces
--   @
--      (v, v') <- instantiateFull (v, v')
--      v == v'
--   @
--   by a more efficient routine which only traverses and instantiates the terms
--   as long as they are equal.

module Agda.TypeChecking.SyntacticEquality (SynEq, checkSyntacticEquality) where

import Prelude hiding (mapM)

import Control.Arrow ((***))
import Control.Monad.State hiding (mapM)

import Agda.Interaction.Options (optSyntacticEquality)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad (ReduceM, MonadReduce(..), pragmaOptions)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad (ifM)


-- | Syntactic equality check for terms.
--   @
--      checkSyntacticEquality v v' = do
--        (v, v') <- instantiateFull (v, v')
--         return ((v, v'), v==v')
--   @
--   only that @v, v'@ are only fully instantiated to the depth
--   where they are equal.

{-# SPECIALIZE checkSyntacticEquality :: Term -> Term -> ReduceM ((Term, Term), Bool) #-}
{-# SPECIALIZE checkSyntacticEquality :: Type -> Type -> ReduceM ((Type, Type), Bool) #-}
checkSyntacticEquality :: (SynEq a, MonadReduce m) => a -> a -> m ((a, a), Bool)
checkSyntacticEquality v v' = liftReduce $ do
  ifM (optSyntacticEquality <$> pragmaOptions)
  {-then-} (synEq v v' `runStateT` True)
  {-else-} (return ((v, v'), False))

-- | Monad for checking syntactic equality
type SynEqM = StateT Bool ReduceM

-- | Return, flagging inequalty.
inequal :: a -> SynEqM a
inequal a = put False >> return a

-- | If inequality is flagged, return, else continue.
ifEqual :: (a -> SynEqM a) -> (a -> SynEqM a)
ifEqual cont a = ifM get (cont a) (return a)

-- Since List2 is only Applicative, not a monad, I cannot
-- define a List2T monad transformer, so we do it manually:

(<$$>) :: Functor f => (a -> b) -> f (a, a) -> f (b, b)
f <$$> xx = (f *** f) <$> xx

pure2 :: Applicative f => a -> f (a, a)
pure2 a = pure (a, a)

(<**>) :: Applicative f => f (a -> b, a -> b) -> f (a, a) -> f (b, b)
ff <**> xx = pure (uncurry (***)) <*> ff <*> xx

-- | Instantiate full as long as things are equal
class SynEq a where
  synEq  :: a -> a -> SynEqM (a, a)
  synEq' :: a -> a -> SynEqM (a, a)
  synEq' a a' = ifEqual (uncurry synEq) (a, a')

instance SynEq Bool where
  synEq x y | x == y = return (x, y)
  synEq x y | otherwise = inequal (x, y)

-- | Syntactic term equality ignores 'DontCare' stuff.
instance SynEq Term where
  synEq v v' = do
    (v, v') <- lift $ instantiate' (v, v')
    case (v, v') of
      (Var   i vs, Var   i' vs') | i == i' -> Var i   <$$> synEq vs vs'
      (Con c i vs, Con c' i' vs') | c == c' -> Con c (bestConInfo i i') <$$> synEq vs vs'
      (Def   f vs, Def   f' vs') | f == f' -> Def f   <$$> synEq vs vs'
      (MetaV x vs, MetaV x' vs') | x == x' -> MetaV x <$$> synEq vs vs'
      (Lit   l   , Lit   l'    ) | l == l' -> pure2 $ v
      (Lam   h b , Lam   h' b' )           -> Lam <$$> synEq h h' <**> synEq b b'
      (Level l   , Level l'    )           -> levelTm <$$> synEq l l'
      (Sort  s   , Sort  s'    )           -> Sort    <$$> synEq s s'
      (Pi    a b , Pi    a' b' )           -> Pi      <$$> synEq a a' <**> synEq' b b'
      (DontCare _, DontCare _  )           -> pure (v, v')
         -- Irrelevant things are syntactically equal. ALT:
         -- DontCare <$$> synEq v v'
      (Dummy{}   , Dummy{}     )           -> pure (v, v')
      _                                    -> inequal (v, v')

instance SynEq Level where
  synEq (Max vs) (Max vs') = levelMax <$$> synEq vs vs'

instance SynEq PlusLevel where
  synEq l l' = do
    case (l, l') of
      (ClosedLevel v, ClosedLevel v') | v == v' -> pure2 l
      (Plus n v,      Plus n' v')     | n == n' -> Plus n <$$> synEq v v'
      _ -> inequal (l, l')

instance SynEq LevelAtom where
  synEq l l' = do
    l  <- lift (unBlock =<< instantiate' l)
    case (l, l') of
      (MetaLevel m vs  , MetaLevel m' vs'  ) | m == m' -> MetaLevel m    <$$> synEq vs vs'
      (UnreducedLevel v, UnreducedLevel v' )           -> UnreducedLevel <$$> synEq v v'
      -- The reason for being blocked should not matter for equality.
      (NeutralLevel r v, NeutralLevel r' v')           -> NeutralLevel r <$$> synEq v v'
      (BlockedLevel m v, BlockedLevel m' v')           -> BlockedLevel m <$$> synEq v v'
      _ -> inequal (l, l')
    where
      unBlock l =
        case l of
          BlockedLevel m v ->
            ifM (isInstantiatedMeta m)
                (pure $ UnreducedLevel v)
                (pure l)
          _ -> pure l

instance SynEq Sort where
  synEq s s' = do
    (s, s') <- lift $ instantiate' (s, s')
    case (s, s') of
      (Type l  , Type l'   ) -> Type <$$> synEq l l'
      (PiSort a b, PiSort a' b') -> piSort <$$> synEq a a' <**> synEq' b b'
      (UnivSort a, UnivSort a') -> UnivSort <$$> synEq a a'
      (SizeUniv, SizeUniv  ) -> pure2 s
      (Prop l  , Prop l'   ) -> Prop <$$> synEq l l'
      (Inf     , Inf       ) -> pure2 s
      (MetaS x es , MetaS x' es') | x == x' -> MetaS x <$$> synEq es es'
      (DefS  d es , DefS  d' es') | d == d' -> DefS d  <$$> synEq es es'
      (DummyS{}, DummyS{}) -> pure (s, s')
      _ -> inequal (s, s')

-- | Syntactic equality ignores sorts.
instance SynEq Type where
  synEq (El s t) (El s' t') = (El s *** El s') <$> synEq t t'

instance SynEq a => SynEq [a] where
  synEq as as'
    | length as == length as' = unzip <$> zipWithM synEq' as as'
    | otherwise               = inequal (as, as')

instance SynEq a => SynEq (Elim' a) where
  synEq e e' =
    case (e, e') of
      (Proj _ f, Proj _ f') | f == f' -> pure2 e
      (Apply a, Apply a') -> Apply <$$> synEq a a'
      (IApply u v r, IApply u' v' r')
                          -> (IApply u v *** IApply u' v') <$> synEq r r'
      _                   -> inequal (e, e')

instance (Subst t a, SynEq a) => SynEq (Abs a) where
  synEq a a' =
    case (a, a') of
      (NoAbs x b, NoAbs x' b') -> (NoAbs x *** NoAbs x') <$>  synEq b b'
      (Abs   x b, Abs   x' b') -> (Abs x *** Abs x') <$> synEq b b'
      (Abs   x b, NoAbs x' b') -> Abs x  <$$> synEq b (raise 1 b')  -- TODO: mkAbs?
      (NoAbs x b, Abs   x' b') -> Abs x' <$$> synEq (raise 1 b) b'

-- NOTE: Do not ignore 'ArgInfo', or test/fail/UnequalHiding will pass.
instance SynEq a => SynEq (Arg a) where
  synEq (Arg ai a) (Arg ai' a') = Arg <$$> synEq ai ai' <**> synEq a a'

-- Ignore the tactic.
instance SynEq a => SynEq (Dom a) where
  synEq d@(Dom ai b x t a) d'@(Dom ai' b' x' _ a')
    | x == x'   = Dom <$$> synEq ai ai' <**> synEq b b' <**> pure2 x <**> pure2 t <**> synEq a a'
    | otherwise = inequal (d, d')

instance SynEq ArgInfo where
  synEq ai@(ArgInfo h r o _) ai'@(ArgInfo h' r' o' _)
    | h == h', r == r' = pure2 ai
    | otherwise        = inequal (ai, ai')
