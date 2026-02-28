{-# OPTIONS_GHC -Wunused-imports #-}

-- | Functions for abstracting terms over other terms.

module Agda.TypeChecking.Abstract where

import Prelude hiding ( null )

import Control.Monad
import Control.Monad.Except

import Data.Function ( on )
import qualified Data.HashMap.Strict as HMap

import Agda.Syntax.Common
import Agda.Syntax.Position ( Range )
import Agda.Syntax.Internal

import Agda.TypeChecking.Free ( freeIn )
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive ( getRefl )
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings ( warning )

import Agda.Utils.Functor
import Agda.Utils.List ( splitExactlyAt, dropEnd )
import Agda.Utils.Null

import Agda.Utils.Impossible

-- | @abstractType r a v b[v] = b@ where @v : a@.
abstractType ::
     Range     -- ^ Range of the @rewrite@ expression, if any, otherwise empty.
  -> Type      -- ^ Type of the term to abstract.
  -> Term      -- ^ Term to abstract.
  -> Type      -- ^ Type to abstract in.
  -> TCM Type  -- ^ Type with hole (de Bruijn index 0) for the abstracted term.
abstractType r a v (El s b) = do

  c <- El (absTerm 0 v s) <$> abstractTerm a v (sort s) b
  unless (null r || 0 `freeIn` c) do
    -- Andreas, 2025-07-03, issue #7973
    -- If with abstraction did not abstract anything, warn the user.
    setCurrentRange r $ warning RewritesNothing
  return c

-- | @piAbstractTerm NotHidden v a b[v] = (w : a) -> b[w]@
--   @piAbstractTerm Hidden    v a b[v] = {w : a} -> b[w]@
piAbstractTerm :: ArgInfo -> Term -> Type -> Type -> TCM Type
piAbstractTerm info v a b = do
  fun <- mkPi (setArgInfo info $ defaultDom ("w", a)) <$> abstractType empty a v b
  reportSDoc "tc.abstract" 50 $
    sep [ "piAbstract" <+> sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ]
        , nest 2 $ "from" <+> prettyTCM b
        , nest 2 $ "-->" <+> prettyTCM fun ]
  reportSDoc "tc.abstract" 70 $
    sep [ "piAbstract" <+> sep [ (text . show) v <+> ":", nest 2 $ (text . show) a ]
        , nest 2 $ "from" <+> (text . show) b
        , nest 2 $ "-->" <+> (text . show) fun ]
  return fun

-- | @piAbstract (v, a) b[v] = (w : a) -> b[w]@
--
--   For the inspect idiom, it does something special:
--   @piAbstract (v, a) b[v, refl v] = (w : a) (w' : Eq a w v) -> b[w, w']
--   (Not all @refl v@ subterms are abstracted: see caveat below.)
--
--   For @rewrite@, it does something special:
--   @piAbstract (prf, Eq a v v') b[v,prf] = (w : a) (w' : Eq a w v') -> b[w, w']@

piAbstract :: Arg (Term, EqualityView) -> Type -> TCM Type
piAbstract (Arg info (v, OtherType a)) b = piAbstractTerm info v a b
piAbstract (Arg info (v, IdiomType a)) b = do
  refl <- getRefl
  eq <- addContext ("w" :: String, defaultDom a) $ do
    -- manufacture the type @w ≡ v@
    eqName <- primEqualityName
    eqTy <- defType <$> getConstInfo eqName
    -- E.g. @eqTy = eqTel → Set a@ where @eqTel = {a : Level} {A : Set a} (x y : A)@.
    TelV eqTel _ <- telView eqTy
    tel  <- newTelMeta (telFromList $ dropEnd 3 $ telToList eqTel)
    let eq = Def eqName $ map Apply
                 $ map (setHiding Hidden) tel
                 -- we write `v ≡ w` because this equality is typically used to
                 -- get `v` to unfold to whatever pattern was used to refine `w`
                 -- in a with-clause.
                 -- If we were to write `w ≡ v`, we would often need to take the
                 -- symmetric of the proof we get to make use of `rewrite`.
                 ++ [ setHiding Hidden $ defaultArg $ raise 1 $ unEl a
                    , defaultArg (raise 1 v)
                    , defaultArg (var 0)
                    ]
    -- Since the result of this function will be type-checked in
    -- `withFunctionType`, we can be a little lazy here and put
    -- a meta for the sort.
    sort <- newSortMeta
    return $ El sort eq

  -- ncf, 2026-01-12: we abstract over v as w first, then over @refl w@
  -- at type @v ≡ w@ so that we only replace those @refl v@ subterms of
  -- the original term that become ill-typed after abstracting v.
  b <- abstractType empty a v b
  b <- addContext ("w" :: String, defaultDom a) $
         abstractType empty eq (refl (defaultArg (var 0))) b

  pure $ mkPi (setHiding (getHiding info) $ defaultDom ("w", a))
       $ mkPi (setHiding NotHidden        $ defaultDom ("eq", eq))
       $ b
piAbstract (Arg info (prf, EqualityViewType eqt@(EqualityTypeData r _ _ _ (Arg _ a) v _))) b = do
  s <- sortOf a
  let prfTy :: Type
      prfTy = equalityUnview eqt
      vTy   = El s a
  -- Andreas, 2025-07-03, issue #7973
  -- We alert the user when the lhs of the equality proof could not be abstracted
  -- but not when the equality proof itself could not be abstracted.
  -- Only the former means that the rewrite did not fire.
  b <- abstractType empty prfTy prf b  -- @empty@ means do not warn
  b <- addContext ("w" :: String, defaultDom prfTy) $
         -- Passing range @r@ here means warn if abstraction failed to abstract anything.
         abstractType r (raise 1 vTy) (unArg $ raise 1 v) b
  return . funType "lhs" vTy . funType "equality" eqTy' . swap01 $ b
  where
    funType str a = mkPi $ setArgInfo info $ defaultDom (str, a)
    -- Abstract the lhs (@a@) of the equality only.
    eqt1 :: EqualityTypeData
    eqt1  = raise 1 eqt
    eqTy' :: Type
    eqTy' = equalityUnview $ eqt1{ _eqtLhs = _eqtLhs eqt1 $> var 0 }


-- | @isPrefixOf u v = Just es@ if @v == u `applyE` es@.
class IsPrefixOf a where
  isPrefixOf :: a -> a -> Maybe Elims

instance IsPrefixOf Elims where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ equalSy us vs1
    return vs2

instance IsPrefixOf Args where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ equalSy us vs1
    return $ map Apply vs2

instance IsPrefixOf Term where
  isPrefixOf u v =
    case (u, v) of
      (Var   i us, Var   j vs) | i == j  -> us `isPrefixOf` vs
      (Def   f us, Def   g vs) | f == g  -> us `isPrefixOf` vs
      (Con c _ us, Con d _ vs) | c == d  -> us `isPrefixOf` vs
      (MetaV x us, MetaV y vs) | x == y  -> us `isPrefixOf` vs
      (u, v) -> guard (equalSy u v) >> return []

-- Type-based abstraction. Needed if @u@ is a constructor application (#745, fix of #5833).
-- Note that @a@ is the type of the new variable, not necessarily the
-- type of @u@: this allows the inspect idiom to abstract over ill-typed
-- subterms of the form @refl w : w ≡ v@ created by abstracting over @v@
-- (see 'piAbstract').
abstractTerm :: Type -> Term -> Type -> Term -> TCM Term
abstractTerm a u@Con{} b v = do
  reportSDoc "tc.abstract" 50 $
    sep [ "Abstracting"
        , nest 2 $ sep [ prettyTCM u <+> ":", nest 2 $ prettyTCM a ]
        , "over"
        , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM b ] ]
  reportSDoc "tc.abstract" 70 $
    sep [ "Abstracting"
        , nest 2 $ sep [ (text . show) u <+> ":", nest 2 $ (text . show) a ]
        , "over"
        , nest 2 $ sep [ (text . show) v <+> ":", nest 2 $ (text . show) b ] ]

  hole <- qualify <$> currentModule <*> freshName_ ("hole" :: String)
  noMutualBlock $ addConstant' hole defaultArgInfo a defaultAxiom

  args <- map Apply <$> getContextArgs
  let n = length args

  let abstr b v = do
        m <- getContextSize
        let (a', u') = raise (m - n) (a, u)
        case u' `isPrefixOf` v of
          Nothing -> return v
          Just es -> do -- Check that the types match.
            s <- getTC
            do  noConstraints $ equalType a' b
                putTC s
                return $ Def hole (raise (m - n) args ++ es)
              `catchError` \ _ -> do
                reportSDoc "tc.abstract.ill-typed" 50 $
                  sep [ "Skipping ill-typed abstraction"
                      , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM b ] ]
                return v

  -- #2763: This can fail if the user is with-abstracting incorrectly (for
  -- instance, abstracting over a first component of a sigma without also
  -- abstracting the second component). In this case we skip abstraction
  -- altogether and let the type check of the final with-function type produce
  -- the error message.
  res <- catchError_ (withFrozenMetas $ checkInternal' (defaultAction { preAction = abstr }) v CmpLeq b) $ \ err -> do
        reportSDoc "tc.abstract.ill-typed" 40 $
          "Skipping typed abstraction over ill-typed term" <?> (prettyTCM v <?> (":" <+> prettyTCM b))
        return v
  reportSDoc "tc.abstract" 50 $ "Resulting abstraction" <?> prettyTCM res
  modifySignature $ updateDefinitions $ HMap.delete hole
  return $ absTerm 0 (Def hole args) res

abstractTerm _ u _ v = return $ absTerm 0 u v -- Non-constructors can use untyped abstraction

class AbsTerm a where
  -- | @subst j u . absTerm j u == id@
  absTerm ::
       Nat   -- ^ De Bruijn index that should be the placeholder for the abstracted term.
    -> Term  -- ^ Term to abstract.
    -> a     -- ^ Where to abstract.
    -> a     -- ^ If the given de Bruijn index is free in the result, abstraction actually happened.

instance AbsTerm Term where
  absTerm j u v
    | Just es <- u `isPrefixOf` v = Var j $ absT es
    | otherwise                   =
    case v of
-- Andreas, 2013-10-20: the original impl. works only at base types
--    v | u == v  -> Var j []  -- incomplete see succeed/WithOfFunctionType
      Var i vs    -> Var (if i < j then i else i + 1) $ absT vs
      Lam h b     -> Lam h $ absT b
      Def c vs    -> Def c $ absT vs
      Con c ci vs -> Con c ci $ absT vs
      Pi a b      -> uncurry Pi $ absT (a, b)
      Lit l       -> Lit l
      Level l     -> Level $ absT l
      Sort s      -> Sort $ absT s
      MetaV m vs  -> MetaV m $ absT vs
      DontCare mv -> DontCare $ absT mv
      Dummy s es   -> Dummy s $ absT es
      where
        absT :: AbsTerm b => b -> b
        absT x = absTerm j u x

instance AbsTerm Type where
  absTerm j u (El s v) = El (absTerm j u s) (absTerm j u v)

instance AbsTerm Sort where
  absTerm j u = \case
    Univ u n   -> Univ u $ absS n
    s@Inf{}    -> s
    SizeUniv   -> SizeUniv
    LockUniv   -> LockUniv
    LevelUniv  -> LevelUniv
    IntervalUniv -> IntervalUniv
    PiSort a s1 s2 -> PiSort (absS a) (absS s1) (absS s2)
    FunSort s1 s2 -> FunSort (absS s1) (absS s2)
    UnivSort s -> UnivSort $ absS s
    MetaS x es -> MetaS x $ absS es
    DefS d es  -> DefS d $ absS es
    s@DummyS{} -> s
    where
      absS :: AbsTerm b => b -> b
      absS x = absTerm j u x

instance AbsTerm Level where
  absTerm j u (Max n as) = Max n $ absTerm j u as

instance AbsTerm PlusLevel where
  absTerm j u (Plus n l) = Plus n $ absTerm j u l

instance AbsTerm a => AbsTerm (Elim' a) where
  absTerm j = fmap . absTerm j

instance AbsTerm a => AbsTerm (Arg a) where
  absTerm j = fmap . absTerm j

instance AbsTerm a => AbsTerm (Dom a) where
  absTerm j = fmap . absTerm j

instance AbsTerm a => AbsTerm [a] where
  absTerm j = fmap . absTerm j

instance AbsTerm a => AbsTerm (Maybe a) where
  absTerm j = fmap . absTerm j

instance (TermSubst a, AbsTerm a) => AbsTerm (Abs a) where
  absTerm j u (NoAbs x v) = NoAbs x $ absTerm j u v
  absTerm j u (Abs   x v) = Abs x $ absTerm (j + 1) (raise 1 u) v

instance (AbsTerm a, AbsTerm b) => AbsTerm (a, b) where
  absTerm j u (x, y) = (absTerm j u x, absTerm j u y)

-- | This swaps @var 0@ and @var 1@.
swap01 :: TermSubst a => a -> a
swap01 = applySubst $ var 1 :# liftS 1 (raiseS 1)


-- ** Equality of terms for the sake of with-abstraction.

-- The following could be parameterized by a record of flags
-- what parts of the syntax tree should be ignored.
-- For now, there is a fixed strategy.

class EqualSy a where
  equalSy :: a -> a -> Bool

instance EqualSy a => EqualSy [a] where
  equalSy us vs = and $ (length us == length vs) : zipWith equalSy us vs

instance EqualSy Term where
  equalSy = curry $ \case
    (Var i   vs, Var i'   vs') -> i == i' && equalSy vs vs'
    (Con c _ es, Con c' _ es') -> c == c' && equalSy es es'
    (Def   f es, Def   f' es') -> f == f' && equalSy es es'
    (MetaV x es, MetaV x' es') -> x == x' && equalSy es es'
    (Lit   l   , Lit   l'    ) -> l == l'
    (Lam   ai b, Lam   ai' b') -> equalSy ai ai' && equalSy b b'
    (Level l   , Level l'    ) -> equalSy l l'
    (Sort  s   , Sort  s'    ) -> equalSy s s'
    (Pi    a b , Pi    a' b' ) -> equalSy a a' && equalSy b b'
    (DontCare _, DontCare _  ) -> True
       -- Irrelevant things are syntactically equal.
    (Dummy{}   , _           ) -> __IMPOSSIBLE__
    (_         , Dummy{}     ) -> __IMPOSSIBLE__
    _ -> False

instance EqualSy Level where
  equalSy (Max n vs) (Max n' vs') = n == n' && equalSy vs vs'

instance EqualSy PlusLevel where
  equalSy (Plus n v) (Plus n' v') = n == n' && equalSy v v'

instance EqualSy Sort where
  equalSy = curry $ \case
    (Univ u l  , Univ u' l'  ) -> u == u' && equalSy l l'
    (Inf u m   , Inf u' n    ) -> u == u' && m == n
    (SizeUniv  , SizeUniv    ) -> True
    (LevelUniv , LevelUniv   ) -> True
    (PiSort a b c, PiSort a' b' c') -> equalSy a a' && equalSy b b' && equalSy c c'
    (FunSort a b, FunSort a' b') -> equalSy a a' && equalSy b b'
    (UnivSort a, UnivSort a' ) -> equalSy a a'
    (MetaS x es, MetaS x' es') -> x == x' && equalSy es es'
    (DefS  d es, DefS  d' es') -> d == d' && equalSy es es'
    (DummyS{}  , _           ) -> __IMPOSSIBLE__
    (_         , DummyS{}    ) -> __IMPOSSIBLE__
    _ -> False

-- | Ignores sorts.
instance EqualSy Type where
  equalSy = equalSy `on` unEl

instance EqualSy a => EqualSy (Elim' a) where
  equalSy = curry $ \case
    (Proj _ f, Proj _ f') -> f == f'
    (Apply a, Apply a') -> equalSy a a'
    (IApply u v r, IApply u' v' r') ->
           equalSy u u'
        && equalSy v v'
        && equalSy r r'
    _ -> False

-- | Ignores 'absName'.
instance (Subst a, EqualSy a) => EqualSy (Abs a) where
  equalSy = curry $ \case
    (NoAbs _x b, NoAbs _x' b') -> equalSy b b' -- no need to raise if both are NoAbs
    (a         , a'          ) -> equalSy (absBody a) (absBody a')

-- | Ignore origin and free variables.
instance EqualSy ArgInfo where
  equalSy (ArgInfo h m _o _fv a) (ArgInfo h' m' _o' _fv' a') =
    h == h' && m == m' && a == a'

-- | Ignore the tactic and rewrite.
instance EqualSy a => EqualSy (Dom a) where
  equalSy d@(Dom ai x f _tac _rew a) d'@(Dom ai' x' f' _tac' _rew' a') = and
    [ x == x'
    , f == f'
    , equalSy ai ai'
    , equalSy a a'
    ]

-- | Ignores irrelevant arguments and modality.
--   (And, of course, origin and free variables).
instance EqualSy a => EqualSy (Arg a) where
  equalSy (Arg (ArgInfo h m _o _fv a) v) (Arg (ArgInfo h' m' _o' _fv' a') v') =
    h == h' && (isIrrelevant m || isIrrelevant m' || equalSy v v')
    -- Andreas, 2017-10-04, issue #2775,
    -- ignore irrelevant arguments during with-abstraction.
    -- 2019-07-05, issue #3889, don't ignore quantity during caching
    -- this is why we let equalSy replace (==).
