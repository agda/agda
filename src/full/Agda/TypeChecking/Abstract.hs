{-# LANGUAGE UndecidableInstances #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract where

import Control.Monad
import Control.Monad.State
import Data.Function
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Pretty

import Agda.Utils.Functor
import Agda.Utils.List (splitExactlyAt)
import Agda.Utils.Size
import Agda.Utils.Except
import qualified Agda.Utils.HashMap as HMap

import Agda.Utils.Impossible

typeOf :: Type -> Type
typeOf = sort . getSort

-- | @abstractType a v b[v] = b@ where @a : v@.
abstractType :: Type -> Term -> Type -> TCM Type
abstractType a v (El s b) = El (absTerm v s) <$> abstractTerm a v (sort s) b

-- | @piAbstractTerm v a b[v] = (w : a) -> b[w]@
piAbstractTerm :: Term -> Type -> Type -> TCM Type
piAbstractTerm v a b = do
  fun <- mkPi (defaultDom ("w", a)) <$> abstractType a v b
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
--   For @rewrite@, it does something special:
--
--   @piAbstract (prf, Eq a v v') b[v,prf] = (w : a) (w' : Eq a w v') -> b[w,w']@

piAbstract :: (Term, EqualityView) -> Type -> TCM Type
piAbstract (v, OtherType a) b = piAbstractTerm v a b
piAbstract (prf, eqt@(EqualityType _ _ _ (Arg _ a) v _)) b = do
  s <- inferSort a
  let prfTy = equalityUnview eqt
      vTy   = El s a
  b <- abstractType prfTy prf b
  b <- addContext ("w" :: String, defaultDom prfTy) $
         abstractType (raise 1 vTy) (unArg $ raise 1 v) b
  return . funType vTy . funType eqTy' . swap01 $ b
  where
    funType a = mkPi $ defaultDom ("w", a)
    -- Abstract the lhs (@a@) of the equality only.
    eqt1  = raise 1 eqt
    eqTy' = equalityUnview $ eqt1 { eqtLhs = eqtLhs eqt1 $> var 0 }

-- | @isPrefixOf u v = Just es@ if @v == u `applyE` es@.
class IsPrefixOf a where
  isPrefixOf :: a -> a -> Maybe Elims

instance IsPrefixOf Elims where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return vs2

instance IsPrefixOf Args where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return $ map Apply vs2

instance IsPrefixOf Term where
  isPrefixOf u v =
    case (u, v) of
      (Var   i us, Var   j vs) | i == j  -> us `isPrefixOf` vs
      (Def   f us, Def   g vs) | f == g  -> us `isPrefixOf` vs
      (Con c _ us, Con d _ vs) | c == d  -> us `isPrefixOf` vs
      (MetaV x us, MetaV y vs) | x == y  -> us `isPrefixOf` vs
      (u, v) -> guard (u == v) >> return []

-- Type-based abstraction. Needed if u is a constructor application (#745).
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
  noMutualBlock $ addConstant hole $ defaultDefn defaultArgInfo hole a Axiom

  args <- map Apply <$> getContextArgs
  let n = length args

  let abstr b v = do
        m <- getContextSize
        let (a', u') = raise (m - n) (a, u)
        case isPrefixOf u' v of
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
  res <- catchError_ (checkInternal' (defaultAction { preAction = abstr }) v b) $ \ err -> do
        reportSDoc "tc.abstract.ill-typed" 40 $
          "Skipping typed abstraction over ill-typed term" <?> (prettyTCM v <?> (":" <+> prettyTCM b))
        return v
  reportSDoc "tc.abstract" 50 $ "Resulting abstraction" <?> prettyTCM res
  modifySignature $ updateDefinitions $ HMap.delete hole
  return $ absTerm (Def hole args) res

abstractTerm _ u _ v = return $ absTerm u v -- Non-constructors can use untyped abstraction

class AbsTerm a where
  -- | @subst u . absTerm u == id@
  absTerm :: Term -> a -> a

instance AbsTerm Term where
  absTerm u v | Just es <- u `isPrefixOf` v = Var 0 $ absT es
              | otherwise                   =
    case v of
-- Andreas, 2013-10-20: the original impl. works only at base types
--    v | u == v  -> Var 0 []  -- incomplete see succeed/WithOfFunctionType
      Var i vs    -> Var (i + 1) $ absT vs
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
        absT x = absTerm u x

instance AbsTerm Type where
  absTerm u (El s v) = El (absTerm u s) (absTerm u v)

instance AbsTerm Sort where
  absTerm u s = case s of
    Type n     -> Type $ absS n
    Prop n     -> Prop $ absS n
    Inf        -> Inf
    SizeUniv   -> SizeUniv
    PiSort s1 s2 -> PiSort (absS s1) (absS s2)
    UnivSort s -> UnivSort $ absS s
    MetaS x es -> MetaS x $ absS es
    DefS d es  -> DefS d $ absS es
    DummyS{}   -> s
    where absS x = absTerm u x

instance AbsTerm Level where
  absTerm u (Max as) = Max $ absTerm u as

instance AbsTerm PlusLevel where
  absTerm u l@ClosedLevel{} = l
  absTerm u (Plus n l) = Plus n $ absTerm u l

instance AbsTerm LevelAtom where
  absTerm u l = case l of
    MetaLevel m vs   -> UnreducedLevel $ absTerm u (MetaV m vs)
    NeutralLevel r v -> NeutralLevel r $ absTerm u v
    BlockedLevel _ v -> UnreducedLevel $ absTerm u v -- abstracting might remove the blockage
    UnreducedLevel v -> UnreducedLevel $ absTerm u v

instance AbsTerm a => AbsTerm (Elim' a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Arg a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Dom a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm [a] where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Maybe a) where
  absTerm = fmap . absTerm

instance (Subst Term a, AbsTerm a) => AbsTerm (Abs a) where
  absTerm u (NoAbs x v) = NoAbs x $ absTerm u v
  absTerm u (Abs   x v) = Abs x $ swap01 $ absTerm (raise 1 u) v

instance (AbsTerm a, AbsTerm b) => AbsTerm (a, b) where
  absTerm u (x, y) = (absTerm u x, absTerm u y)

-- | This swaps @var 0@ and @var 1@.
swap01 :: (Subst Term a) => a -> a
swap01 = applySubst $ var 1 :# liftS 1 (raiseS 1)
