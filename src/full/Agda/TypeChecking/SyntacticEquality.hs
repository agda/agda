{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
#if  __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}
#endif
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

-- | A syntactic equality check that takes meta instantiations into account,
--   but does not reduce.  It replaces
--   @
--      (v, v') <- instantiateFull (v, v')
--      v == v'
--   @
--   by a more efficient routine which only traverses and instantiates the terms
--   as long as they are equal.

module Agda.TypeChecking.SyntacticEquality
  ( SynEq
  , checkSyntacticEquality
  , checkSyntacticEquality'
  , syntacticEqualityFuelRemains
  )
  where

import Control.Monad
import Control.Monad.Trans      ( lift )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.ExpandCase
import Agda.Utils.Maybe.Strict  qualified as Strict
import Agda.Utils.Monad         ( ifM )
import Agda.Utils.Unsafe        ( unsafeComparePointers )
import Agda.Utils.Tuple         ( (***) )
import Agda.Utils.StrictState


-- | Syntactic equality check for terms. If syntactic equality
-- checking has fuel left, then 'checkSyntacticEquality' behaves as if
-- it were implemented in the following way (which does not match the
-- given type signature), only that @v@ and @v'@ are only fully
-- instantiated to the depth where they are equal (and the amount of
-- fuel is reduced by one unit in the failure branch):
--   @
--      checkSyntacticEquality v v' s f = do
--        (v, v') <- instantiateFull (v, v')
--        if v == v' then s v v' else f v v'
--   @
-- If syntactic equality checking does not have fuel left, then
-- 'checkSyntacticEquality' instantiates the two terms and takes the
-- failure branch.
--
-- Note that in either case the returned values @v@ and @v'@ cannot be
-- @MetaV@s that are instantiated.

{-# SPECIALIZE checkSyntacticEquality ::
      Term -> Term ->
      (Term -> Term -> ReduceM a) ->
      (Term -> Term -> ReduceM a) ->
      ReduceM a #-}
{-# SPECIALIZE checkSyntacticEquality ::
      Type -> Type ->
      (Type -> Type -> TCM a) ->
      (Type -> Type -> TCM a) ->
      TCM a #-}
checkSyntacticEquality
  :: (Instantiate a, SynEq a, MonadReduce m)
  => a
  -> a
  -> (a -> a -> m b)  -- ^ Continuation used upon success.
  -> (a -> a -> m b)  -- ^ Continuation used upon failure, or if
                      --   syntactic equality checking has been turned
                      --   off.
  -> m b
checkSyntacticEquality u v s f =
  ifM syntacticEqualityFuelRemains
  {-then-} (checkSyntacticEquality' u v s (\u v -> localTC decreaseFuel (f u v)))
  {-else-} (uncurry f =<< instantiate (u, v))
  where
  decreaseFuel env =
    case env ^. eSyntacticEqualityFuel of
      Strict.Nothing -> env
      Strict.Just n  -> env & eSyntacticEqualityFuel .~ Strict.Just (pred n)

-- | Syntactic equality check for terms without checking remaining fuel.
checkSyntacticEquality'
  :: (SynEq a, MonadReduce m)
  => a
  -> a
  -> (a -> a -> m b)  -- ^ Continuation used upon success.
  -> (a -> a -> m b)  -- ^ Continuation used upon failure.
  -> m b
checkSyntacticEquality' u v s f = do
  ((u, v), equal) <- liftReduce $ synEq u v `runStateT` True
  if equal then s u v else f u v

-- | Does the syntactic equality check have any remaining fuel?

syntacticEqualityFuelRemains :: MonadReduce m => m Bool
syntacticEqualityFuelRemains = do
  fuel <- viewTC eSyntacticEqualityFuel
  return $! case fuel of
    Strict.Nothing -> True
    Strict.Just n  -> n > 0

-- | Monad for checking syntactic equality
type SynEqM = StateT Bool ReduceM

-- | Return, flagging inequalty.
inequal :: a -> SynEqM a
inequal a = put False >> return a

-- Since List2 is only Applicative, not a monad, I cannot
-- define a List2T monad transformer, so we do it manually:
{-# INLINE (<$$>) #-}
(<$$>) :: Monad f => (a -> b) -> f (a, a) -> f (b, b)
f <$$> aa = do
  (a, a') <- aa
  let b  = f a
  let b' = f a'
  pure (b, b')

pure2 :: Applicative f => a -> f (a, a)
pure2 a = pure (a, a)

{-# INLINE (<**>) #-}
(<**>) :: Monad f => f (a -> b, a -> b) -> f (a, a) -> f (b, b)
ff <**> aa = do
  (f, f') <- ff
  (a, a') <- aa
  let b = f a
  let b' = f' a'
  pure (b, b')

-- | Instantiate full as long as things are equal
class SynEq a where
  synEq  :: a -> a -> SynEqM (a, a)

  {-# INLINE synEq' #-}
  synEq' :: a -> a -> SynEqM (a, a)
  synEq' a a' = do
    eq <- get
    expand \ret -> if eq then ret $ synEq a a'
                         else ret $ pure (a, a')

instance SynEq Bool where
  synEq x y = expand \ret -> if x == y then ret $ pure (x, y) else ret $ inequal (x, y)

-- | Syntactic term equality ignores 'DontCare' stuff.
instance SynEq Term where
  synEq v v' = expand \ret -> if unsafeComparePointers v v' then ret $ pure (v, v') else ret do
    (v, v') <- lift $ instantiate' (v, v')
    expand \ret -> case (v, v') of
      (Var   i vs, Var   i' vs')  | i == i' -> ret $ Var i   <$$> synEq vs vs'
      (Con c i vs, Con c' i' vs') | c == c' -> ret $ Con c (bestConInfo i i') <$$> synEq vs vs'
      (Def   f vs, Def   f' vs')  | f == f' -> ret $ Def f   <$$> synEq vs vs'
      (MetaV x vs, MetaV x' vs')  | x == x' -> ret $ MetaV x <$$> synEq vs vs'
      (Lit   l   , Lit   l'    )  | l == l' -> ret $ pure2 $ v
      (Lam   h b , Lam   h' b' )            -> ret $ Lam <$$> synEq h h' <**> synEq b b'
      (Level l   , Level l'    )            -> ret $ levelTm <$$> synEq l l'
      (Sort  s   , Sort  s'    )            -> ret $ Sort    <$$> synEq s s'
      (Pi    a b , Pi    a' b' )            -> ret $ Pi      <$$> synEq a a' <**> synEq' b b'
      (DontCare u, DontCare u' )            -> ret $ DontCare <$$> synEq u u'
         -- Irrelevant things are not syntactically equal. ALT:
         -- pure (u, u')
         -- Jesper, 2019-10-21: considering irrelevant things to be
         -- syntactically equal causes implicit arguments to go
         -- unsolved, so it is better to go under the DontCare.
      (Dummy{}   , Dummy{}     )            -> ret $ pure (v, v')
      _                                     -> ret $ inequal (v, v')

instance SynEq Level where
  synEq l l' = expand \ret -> case (l, l') of
    (l@(Max n vs), l'@(Max n' vs'))
      | n == n'   -> ret $ levelMax n <$$> synEq vs vs'
      | otherwise -> ret $ inequal (l, l')

instance SynEq PlusLevel where
  synEq l l' = expand \ret -> case (l, l') of
    (l@(Plus n v), l'@(Plus n' v'))
      | n == n'   -> ret $ Plus n <$$> synEq v v'
      | otherwise -> ret $ inequal (l, l')

instance SynEq Sort where
  synEq s s' = expand \ret -> if unsafeComparePointers s s' then ret $ pure (s, s') else ret do
    (s, s') <- lift $ instantiate' (s, s')
    expand \ret -> case (s, s') of
      (Univ u l, Univ u' l') | u == u' -> ret $ Univ u <$$> synEq l l'
      (PiSort a b c, PiSort a' b' c') -> ret $ PiSort <$$> synEq a a' <**> synEq' b b' <**> synEq' c c'
      (FunSort a b, FunSort a' b') -> ret $ FunSort <$$> synEq a a' <**> synEq' b b'
      (UnivSort a, UnivSort a') -> ret $ UnivSort <$$> synEq a a'
      (SizeUniv, SizeUniv  ) -> ret $ pure2 s
      (LockUniv, LockUniv  ) -> ret $ pure2 s
      (LevelUniv, LevelUniv  ) -> ret $ pure2 s
      (IntervalUniv, IntervalUniv) -> ret $ pure2 s
      (Inf u m , Inf u' n) | u == u', m == n -> ret $ pure2 s
      (MetaS x es , MetaS x' es') | x == x' -> ret $ MetaS x <$$> synEq es es'
      (DefS  d es , DefS  d' es') | d == d' -> ret $ DefS d  <$$> synEq es es'
      (DummyS{}, DummyS{}) -> ret $ pure (s, s')
      _ -> ret $ inequal (s, s')

-- | Syntactic equality ignores sorts.
instance SynEq Type where
  synEq x y = expand \ret -> case (x, y) of
    (El s t, El s' t') -> ret $ (El s *** El s') <$!> synEq t t'

instance SynEq a => SynEq [a] where
  synEq as as' = expand \ret -> case (as, as') of
    ([], [])       -> ret $ pure ([], [])
    (a:as, a':as') -> ret $ (:) <$$> synEq a a' <**> synEq as as'
    (as, as')      -> ret $ inequal (as, as')

instance (SynEq a, SynEq b) => SynEq (a,b) where
  synEq x y = expand \ret -> case (x, y) of
    ((a,b), (a',b')) -> ret $ (,) <$$> synEq a a' <**> synEq b b'

instance SynEq a => SynEq (Elim' a) where
  synEq e e' = expand \ret ->
    case (e, e') of
      (Proj _ f, Proj _ f') | f == f' -> ret $ pure2 e
      (Apply a, Apply a') -> ret $ Apply <$$> synEq a a'
      (IApply u v r, IApply u' v' r')
                          -> ret $ (IApply u v *** IApply u' v') <$!> synEq r r'
      _                   -> ret $ inequal (e, e')

instance (Subst a, SynEq a) => SynEq (Abs a) where
  synEq a a' = expand \ret ->
    case (a, a') of
      (NoAbs x b, NoAbs x' b') -> ret $ (NoAbs x *** NoAbs x') <$!>  synEq b b'
      (Abs   x b, Abs   x' b') -> ret $ (Abs x *** Abs x') <$!> synEq b b'
      (Abs   x b, NoAbs x' b') -> ret $ Abs x  <$$> synEq b (raise 1 b')  -- TODO: mkAbs?
      (NoAbs x b, Abs   x' b') -> ret $ Abs x' <$$> synEq (raise 1 b) b'

-- NOTE: Do not ignore 'ArgInfo', or test/fail/UnequalHiding will pass.
instance SynEq a => SynEq (Arg a) where
  synEq x y = expand \ret -> case (x, y) of
    ((Arg ai a), (Arg ai' a')) -> ret $ Arg <$$> synEq ai ai' <**> synEq a a'

-- Ignore the tactic and elaborated rewrite.
instance SynEq a => SynEq (Dom a) where
  synEq d d' = expand \ret -> case (d, d') of
    (d@(Dom ai x f t r a), d'@(Dom ai' x' f' _ r' a'))
      | x == x'   -> ret $ Dom <$$> synEq ai ai' <**> pure2 x <**> synEq f f'
                               <**> pure2 t <**> pure (r, r') <**> synEq a a'
      | otherwise -> ret $ inequal (d, d')

instance SynEq ArgInfo where
  synEq ai ai' = expand \ret -> case (ai, ai') of
    (ai@(ArgInfo h r o _ a), ai'@(ArgInfo h' r' o' _ a'))
      | h == h', sameModality r r', a == a' -> ret $ pure2 ai
      | otherwise                           -> ret $ inequal (ai, ai')
