{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NondecreasingIndentation   #-}
{-# LANGUAGE MonoLocalBinds             #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive
       ( module Agda.TypeChecking.Primitive.Base
       , module Agda.TypeChecking.Primitive.Cubical
       , module Agda.TypeChecking.Primitive
       ) where

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Word

import qualified Agda.Interaction.Options.Lenses as Lens

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Literal
import Agda.Syntax.Fixity

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level

import Agda.TypeChecking.Quote (quoteTermWithKit, quoteTypeWithKit, quotingKit)
import Agda.TypeChecking.Pretty ()  -- instances only
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Warnings

import Agda.Utils.Float
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.String ( Str(Str), unStr )

import Agda.Utils.Impossible

-- Haskell type to Agda type

newtype Nat = Nat { unNat :: Integer }
            deriving (Eq, Ord, Num, Enum, Real)

-- In GHC > 7.8 deriving Integral causes an unnecessary toInteger
-- warning.
instance Integral Nat where
  toInteger = unNat
  quotRem (Nat a) (Nat b) = (Nat q, Nat r)
    where (q, r) = quotRem a b

instance TermLike Nat where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance Show Nat where
  show = show . toInteger

newtype Lvl = Lvl { unLvl :: Integer }
  deriving (Eq, Ord)

instance Show Lvl where
  show = show . unLvl

class PrimType a where
  primType :: a -> TCM Type

instance (PrimType a, PrimType b) => PrimTerm (a -> b) where
  primTerm _ = unEl <$> (primType (undefined :: a) --> primType (undefined :: b))

instance (PrimType a, PrimType b) => PrimTerm (a, b) where
  primTerm _ = do
    sigKit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
    let sig = Def (sigmaName sigKit) []
    a'       <- primType (undefined :: a)
    b'       <- primType (undefined :: b)
    Type la  <- pure $ getSort a'
    Type lb  <- pure $ getSort b'
    pure sig <#> pure (Level la)
             <#> pure (Level lb)
             <@> pure (unEl a')
             <@> pure (nolam $ unEl b')

instance PrimTerm a => PrimType a where
  primType _ = el $ primTerm (undefined :: a)

class    PrimTerm a       where primTerm :: a -> TCM Term
instance PrimTerm Integer where primTerm _ = primInteger
instance PrimTerm Word64  where primTerm _ = primWord64
instance PrimTerm Bool    where primTerm _ = primBool
instance PrimTerm Char    where primTerm _ = primChar
instance PrimTerm Double  where primTerm _ = primFloat
instance PrimTerm Str     where primTerm _ = primString
instance PrimTerm Nat     where primTerm _ = primNat
instance PrimTerm Lvl     where primTerm _ = primLevel
instance PrimTerm QName   where primTerm _ = primQName
instance PrimTerm MetaId  where primTerm _ = primAgdaMeta
instance PrimTerm Type    where primTerm _ = primAgdaTerm

instance PrimTerm Fixity' where primTerm _ = primFixity

instance PrimTerm a => PrimTerm [a] where
  primTerm _ = list (primTerm (undefined :: a))

instance PrimTerm a => PrimTerm (IO a) where
  primTerm _ = io (primTerm (undefined :: a))

-- From Agda term to Haskell value

class ToTerm a where
  toTerm  :: TCM (a -> Term)
  toTermR :: TCM (a -> ReduceM Term)

  toTermR = (pure .) <$> toTerm

instance ToTerm Nat     where toTerm = return $ Lit . LitNat noRange . toInteger
instance ToTerm Word64  where toTerm = return $ Lit . LitWord64 noRange
instance ToTerm Lvl     where toTerm = return $ Level . Max . (:[]) . ClosedLevel . unLvl
instance ToTerm Double  where toTerm = return $ Lit . LitFloat noRange
instance ToTerm Char    where toTerm = return $ Lit . LitChar noRange
instance ToTerm Str     where toTerm = return $ Lit . LitString noRange . unStr
instance ToTerm QName   where toTerm = return $ Lit . LitQName noRange
instance ToTerm MetaId  where
  toTerm = do
    file <- getCurrentPath
    return $ Lit . LitMeta noRange file

instance ToTerm Integer where
  toTerm = do
    pos     <- primIntegerPos
    negsuc  <- primIntegerNegSuc
    fromNat <- toTerm :: TCM (Nat -> Term)
    let intToTerm = fromNat . fromIntegral :: Integer -> Term
    let fromInt n | n >= 0    = apply pos    [defaultArg $ intToTerm n]
                  | otherwise = apply negsuc [defaultArg $ intToTerm (-n - 1)]
    return fromInt

instance ToTerm Bool where
  toTerm = do
    true  <- primTrue
    false <- primFalse
    return $ \b -> if b then true else false

instance ToTerm Term where
  toTerm  = do kit <- quotingKit; runReduceF (quoteTermWithKit kit)
  toTermR = do kit <- quotingKit; return (quoteTermWithKit kit)

instance ToTerm Type where
  toTerm  = do kit <- quotingKit; runReduceF (quoteTypeWithKit kit)
  toTermR = do kit <- quotingKit; return (quoteTypeWithKit kit)

instance ToTerm ArgInfo where
  toTerm = do
    info <- primArgArgInfo
    vis  <- primVisible
    hid  <- primHidden
    ins  <- primInstance
    rel  <- primRelevant
    irr  <- primIrrelevant
    return $ \ i -> info `applys`
      [ case getHiding i of
          NotHidden  -> vis
          Hidden     -> hid
          Instance{} -> ins
      , case getRelevance i of
          Relevant   -> rel
          Irrelevant -> irr
          NonStrict  -> rel
      ]

instance ToTerm Fixity' where
  toTerm = (. theFixity) <$> toTerm

instance ToTerm Fixity where
  toTerm = do
    lToTm  <- toTerm
    aToTm  <- toTerm
    fixity <- primFixityFixity
    return $ \ Fixity{fixityAssoc = a, fixityLevel = l} ->
      fixity `apply` [defaultArg (aToTm a), defaultArg (lToTm l)]

instance ToTerm Associativity where
  toTerm = do
    lassoc <- primAssocLeft
    rassoc <- primAssocRight
    nassoc <- primAssocNon
    return $ \ a ->
      case a of
        NonAssoc   -> nassoc
        LeftAssoc  -> lassoc
        RightAssoc -> rassoc

instance ToTerm FixityLevel where
  toTerm = do
    (iToTm :: PrecedenceLevel -> Term) <- toTerm
    related   <- primPrecRelated
    unrelated <- primPrecUnrelated
    return $ \ p ->
      case p of
        Unrelated -> unrelated
        Related n -> related `apply` [defaultArg $ iToTm n]

instance (ToTerm a, ToTerm b) => ToTerm (a, b) where
  toTerm = do
    sigKit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
    let con = Con (sigmaCon sigKit) ConOSystem []
    fromA <- toTerm
    fromB <- toTerm
    pure $ \ (a, b) -> con `apply` map defaultArg [fromA a, fromB b]

-- | @buildList A ts@ builds a list of type @List A@. Assumes that the terms
--   @ts@ all have type @A@.
buildList :: TCM ([Term] -> Term)
buildList = do
    nil'  <- primNil
    cons' <- primCons
    let nil       = nil'
        cons x xs = cons' `applys` [x, xs]
    return $ foldr cons nil

instance ToTerm a => ToTerm [a] where
  toTerm = do
    mkList <- buildList
    fromA  <- toTerm
    return $ mkList . map fromA

-- From Haskell value to Agda term

type FromTermFunction a = Arg Term ->
                          ReduceM (Reduced (MaybeReduced (Arg Term)) a)

class FromTerm a where
  fromTerm :: TCM (FromTermFunction a)

instance FromTerm Integer where
  fromTerm = do
    Con pos _    [] <- primIntegerPos
    Con negsuc _ [] <- primIntegerNegSuc
    toNat         <- fromTerm :: TCM (FromTermFunction Nat)
    return $ \ v -> do
      b <- reduceB' v
      let v'  = ignoreBlocking b
          arg = (<$ v')
      case unArg (ignoreBlocking b) of
        Con c ci [Apply u]
          | c == pos    ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c ci [Apply $ ignoreReduced u']) $ \ n ->
            redReturn $ fromIntegral n
          | c == negsuc ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c ci [Apply $ ignoreReduced u']) $ \ n ->
            redReturn $ fromIntegral $ -n - 1
        _ -> return $ NoReduction (reduced b)

instance FromTerm Nat where
  fromTerm = fromLiteral $ \l -> case l of
    LitNat _ n -> Just $ fromInteger n
    _          -> Nothing

instance FromTerm Word64 where
  fromTerm = fromLiteral $ \ case
    LitWord64 _ n -> Just n
    _             -> Nothing

instance FromTerm Lvl where
  fromTerm = fromReducedTerm $ \l -> case l of
    Level (Max [ClosedLevel n]) -> Just $ Lvl n
    _                           -> Nothing

instance FromTerm Double where
  fromTerm = fromLiteral $ \l -> case l of
    LitFloat _ x -> Just x
    _            -> Nothing

instance FromTerm Char where
  fromTerm = fromLiteral $ \l -> case l of
    LitChar _ c -> Just c
    _           -> Nothing

instance FromTerm Str where
  fromTerm = fromLiteral $ \l -> case l of
    LitString _ s -> Just $ Str s
    _             -> Nothing

instance FromTerm QName where
  fromTerm = fromLiteral $ \l -> case l of
    LitQName _ x -> Just x
    _             -> Nothing

instance FromTerm MetaId where
  fromTerm = fromLiteral $ \l -> case l of
    LitMeta _ _ x -> Just x
    _             -> Nothing

instance FromTerm Bool where
    fromTerm = do
        true  <- primTrue
        false <- primFalse
        fromReducedTerm $ \t -> case t of
            _   | t =?= true  -> Just True
                | t =?= false -> Just False
                | otherwise   -> Nothing
        where
            a =?= b = a === b
            Def x [] === Def y []   = x == y
            Con x _ [] === Con y _ [] = x == y
            Var n [] === Var m []   = n == m
            _        === _          = False

instance (ToTerm a, FromTerm a) => FromTerm [a] where
  fromTerm = do
    nil'  <- primNil
    cons' <- primCons
    nil   <- isCon nil'
    cons  <- isCon cons'
    toA   <- fromTerm
    fromA <- toTerm
    return $ mkList nil cons toA fromA
    where
      isCon (Lam _ b)  = isCon $ absBody b
      isCon (Con c _ _)= return c
      isCon v          = __IMPOSSIBLE__

      mkList nil cons toA fromA t = do
        b <- reduceB' t
        let t = ignoreBlocking b
        let arg = (<$ t)
        case unArg t of
          Con c ci []
            | c == nil  -> return $ YesReduction NoSimplification []
          Con c ci es
            | c == cons, Just [x,xs] <- allApplyElims es ->
              redBind (toA x)
                  (\x' -> notReduced $ arg $ Con c ci (map Apply [ignoreReduced x',xs])) $ \y ->
              redBind
                  (mkList nil cons toA fromA xs)
                  (fmap $ \xs' -> arg $ Con c ci (map Apply [defaultArg $ fromA y, xs'])) $ \ys ->
              redReturn (y : ys)
          _ -> return $ NoReduction (reduced b)

fromReducedTerm :: (Term -> Maybe a) -> TCM (FromTermFunction a)
fromReducedTerm f = return $ \t -> do
    b <- reduceB' t
    case f $ unArg (ignoreBlocking b) of
        Just x  -> return $ YesReduction NoSimplification x
        Nothing -> return $ NoReduction (reduced b)

fromLiteral :: (Literal -> Maybe a) -> TCM (FromTermFunction a)
fromLiteral f = fromReducedTerm $ \t -> case t of
    Lit lit -> f lit
    _       -> Nothing

-- | @mkPrimInjective@ takes two Set0 @a@ and @b@ and a function @f@ of type
--   @a -> b@ and outputs a primitive internalizing the fact that @f@ is injective.
mkPrimInjective :: Type -> Type -> QName -> TCM PrimitiveImpl
mkPrimInjective a b qn = do
  -- Define the type
  eqName <- primEqualityName
  let lvl0     = Max []
  let eq a t u = El (Type lvl0) <$> pure (Def eqName []) <#> pure (Level lvl0)
                                <#> pure (unEl a) <@> t <@> u
  let f    = pure (Def qn [])
  ty <- nPi "t" (pure a) $ nPi "u" (pure a) $
              (eq b (f <@> varM 1) (f <@> varM 0))
          --> (eq a (      varM 1) (      varM 0))

    -- Get the constructor corresponding to BUILTIN REFL
  refl <- getRefl

  -- Implementation: when the equality argument reduces to refl so does the primitive.
  -- If the user want the primitive to reduce whenever the two values are equal (no
  -- matter whether the equality is refl), they can combine it with @eraseEquality@.
  return $ PrimImpl ty $ primFun __IMPOSSIBLE__ 3 $ \ ts -> do
    let t  = headWithDefault __IMPOSSIBLE__ ts
    let eq = unArg $ fromMaybe __IMPOSSIBLE__ $ lastMaybe ts
    eq' <- normalise' eq
    case eq' of
      Con{} -> redReturn $ refl t
      _     -> return $ NoReduction $ map notReduced ts

primMetaToNatInjective :: TCM PrimitiveImpl
primMetaToNatInjective = do
  meta  <- primType (undefined :: MetaId)
  nat   <- primType (undefined :: Nat)
  toNat <- primFunName <$> getPrimitive "primMetaToNat"
  mkPrimInjective meta nat toNat

primCharToNatInjective :: TCM PrimitiveImpl
primCharToNatInjective = do
  char  <- primType (undefined :: Char)
  nat   <- primType (undefined :: Nat)
  toNat <- primFunName <$> getPrimitive "primCharToNat"
  mkPrimInjective char nat toNat

primStringToListInjective :: TCM PrimitiveImpl
primStringToListInjective = do
  string <- primType (undefined :: Str)
  chars  <- primType (undefined :: String)
  toList <- primFunName <$> getPrimitive "primStringToList"
  mkPrimInjective string chars toList

primWord64ToNatInjective :: TCM PrimitiveImpl
primWord64ToNatInjective =  do
  word  <- primType (undefined :: Word64)
  nat   <- primType (undefined :: Nat)
  toNat <- primFunName <$> getPrimitive "primWord64ToNat"
  mkPrimInjective word nat toNat

primFloatToWord64Injective :: TCM PrimitiveImpl
primFloatToWord64Injective = do
  float  <- primType (undefined :: Double)
  word   <- primType (undefined :: Word64)
  toWord <- primFunName <$> getPrimitive "primFloatToWord64"
  mkPrimInjective float word toWord

primQNameToWord64sInjective :: TCM PrimitiveImpl
primQNameToWord64sInjective = do
  name    <- primType (undefined :: QName)
  words   <- primType (undefined :: (Word64, Word64))
  toWords <- primFunName <$> getPrimitive "primQNameToWord64s"
  mkPrimInjective name words toWords

getRefl :: TCM (Arg Term -> Term)
getRefl = do
  -- BUILTIN REFL maybe a constructor with one (the principal) argument or only parameters.
  -- Get the ArgInfo of the principal argument of refl.
  con@(Con rf ci []) <- primRefl
  minfo <- fmap (setOrigin Inserted) <$> getReflArgInfo rf
  pure $ case minfo of
    Just ai -> Con rf ci . (:[]) . Apply . setArgInfo ai
    Nothing -> const con

-- | @primEraseEquality : {a : Level} {A : Set a} {x y : A} -> x ≡ y -> x ≡ y@
primEraseEquality :: TCM PrimitiveImpl
primEraseEquality = do
  -- primEraseEquality is incompatible with --without-K
  -- We raise an error warning if --safe is set and a mere warning otherwise
  whenM withoutKOption $
    ifM (Lens.getSafeMode <$> commandLineOptions)
      {- then -} (warning SafeFlagWithoutKFlagPrimEraseEquality)
      {- else -} (warning WithoutKFlagPrimEraseEquality)
  -- Get the name and type of BUILTIN EQUALITY
  eq   <- primEqualityName
  eqTy <- defType <$> getConstInfo eq
  -- E.g. @eqTy = eqTel → Set a@ where @eqTel = {a : Level} {A : Set a} (x y : A)@.
  TelV eqTel eqCore <- telView eqTy
  let eqSort = case unEl eqCore of
        Sort s -> s
        _      -> __IMPOSSIBLE__

  -- Construct the type of primEraseEquality, e.g.
  -- @{a : Level} {A : Set a} {x y : A} → eq {a} {A} x y -> eq {a} {A} x y@.
  t <- let xeqy = pure $ El eqSort $ Def eq $ map Apply $ teleArgs eqTel in
       telePi_ (fmap hide eqTel) <$> (xeqy --> xeqy)

  -- Get the constructor corresponding to BUILTIN REFL
  refl <- getRefl

  -- The implementation of primEraseEquality:
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ (1 + size eqTel) $ \ ts -> do
    let (u, v) = fromMaybe __IMPOSSIBLE__ $ last2 =<< initMaybe ts
    -- Andreas, 2013-07-22.
    -- Note that we cannot call the conversion checker here,
    -- because 'reduce' might be called in a context where
    -- some bound variables do not have a type (just __DUMMY_TYPE__),
    -- and the conversion checker for eliminations does not
    -- like this.
    -- We can only do untyped equality, e.g., by normalisation.
    (u', v') <- normalise' (u, v)
    if u' == v' then redReturn $ refl u else
      return $ NoReduction $ map notReduced ts

-- | Get the 'ArgInfo' of the principal argument of BUILTIN REFL.
--
--   Returns @Nothing@ for e.g.
--   @
--     data Eq {a} {A : Set a} (x : A) : A → Set a where
--       refl : Eq x x
--   @
--
--   Returns @Just ...@ for e.g.
--   @
--     data Eq {a} {A : Set a} : (x y : A) → Set a where
--       refl : ∀ x → Eq x x
--   @

getReflArgInfo :: ConHead -> TCM (Maybe ArgInfo)
getReflArgInfo rf = do
  def <- getConInfo rf
  TelV reflTel _ <- telView $ defType def
  return $ fmap getArgInfo $ listToMaybe $ drop (conPars $ theDef def) $ telToList reflTel


-- | Used for both @primForce@ and @primForceLemma@.
genPrimForce :: TCM Type -> (Term -> Arg Term -> Term) -> TCM PrimitiveImpl
genPrimForce b ret = do
  let varEl s a = El (varSort s) <$> a
      varT s a  = varEl s (varM a)
      varS s    = pure $ sort $ varSort s
  t <- hPi "a" (el primLevel) $
       hPi "b" (el primLevel) $
       hPi "A" (varS 1) $
       hPi "B" (varT 2 0 --> varS 1) b
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts ->
    case ts of
      [a, b, s, t, u, f] -> do
        u <- reduceB' u
        let isWHNF Blocked{} = return False
            isWHNF (NotBlocked _ u) =
              case unArg u of
                Lit{}      -> return True
                Con{}      -> return True
                Lam{}      -> return True
                Pi{}       -> return True
                Sort{}     -> return True  -- sorts and levels are considered whnf
                Level{}    -> return True
                DontCare{} -> return True
                Def q _    -> do
                  def <- theDef <$> getConstInfo q
                  return $ case def of
                    Datatype{} -> True
                    Record{}   -> True
                    _          -> False
                MetaV{}    -> return False
                Var{}      -> return False
                Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s
        ifM (isWHNF u)
            (redReturn $ ret (unArg f) (ignoreBlocking u))
            (return $ NoReduction $ map notReduced [a, b, s, t] ++ [reduced u, notReduced f])
      _ -> __IMPOSSIBLE__

primForce :: TCM PrimitiveImpl
primForce = do
  let varEl s a = El (varSort s) <$> a
      varT s a  = varEl s (varM a)
      varS s    = pure $ sort $ varSort s
  genPrimForce (nPi "x" (varT 3 1) $
                (nPi "y" (varT 4 2) $ varEl 4 $ varM 2 <@> varM 0) -->
                varEl 3 (varM 1 <@> varM 0)) $
    \ f u -> apply f [u]

primForceLemma :: TCM PrimitiveImpl
primForceLemma = do
  let varEl s a = El (varSort s) <$> a
      varT s a  = varEl s (varM a)
      varS s    = pure $ sort $ varSort s
  refl  <- primRefl
  force <- primFunName <$> getPrimitive "primForce"
  genPrimForce (nPi "x" (varT 3 1) $
                nPi "f" (nPi "y" (varT 4 2) $ varEl 4 $ varM 2 <@> varM 0) $
                varEl 4 $ primEquality <#> varM 4 <#> (varM 2 <@> varM 1)
                                       <@> (pure (Def force []) <#> varM 5 <#> varM 4 <#> varM 3 <#> varM 2 <@> varM 1 <@> varM 0)
                                       <@> (varM 0 <@> varM 1)
               ) $ \ _ _ -> refl

mkPrimLevelZero :: TCM PrimitiveImpl
mkPrimLevelZero = do
  t <- primType (undefined :: Lvl)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Level $ Max []

mkPrimLevelSuc :: TCM PrimitiveImpl
mkPrimLevelSuc = do
  t <- primType (id :: Lvl -> Lvl)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ ~[a] -> do
    l <- levelView' $ unArg a
    redReturn $ Level $ levelSuc l

mkPrimLevelMax :: TCM PrimitiveImpl
mkPrimLevelMax = do
  t <- primType (max :: Op Lvl)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \ ~[a, b] -> do
    Max as <- levelView' $ unArg a
    Max bs <- levelView' $ unArg b
    redReturn $ Level $ levelMax $ as ++ bs

mkPrimSetOmega :: TCM PrimitiveImpl
mkPrimSetOmega = do
  let t = sort $ UnivSort Inf
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Sort Inf

mkPrimFun1TCM :: (FromTerm a, ToTerm b, TermLike b) =>
                 TCM Type -> (a -> ReduceM b) -> TCM PrimitiveImpl
mkPrimFun1TCM mt f = do
    toA   <- fromTerm
    fromB <- toTermR
    t     <- mt
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ts ->
      case ts of
        [v] ->
          redBind (toA v) singleton $ \ x -> do
            b <- f x
            case firstMeta b of
              Just m  -> return $ NoReduction [reduced (Blocked m v)]
              Nothing -> redReturn =<< fromB b
        _ -> __IMPOSSIBLE__

-- Tying the knot
mkPrimFun1 :: (PrimType a, FromTerm a, PrimType b, ToTerm b) =>
              (a -> b) -> TCM PrimitiveImpl
mkPrimFun1 f = do
    toA   <- fromTerm
    fromB <- toTerm
    t     <- primType f
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ts ->
      case ts of
        [v] ->
          redBind (toA v) singleton $ \ x ->
          redReturn $ fromB $ f x
        _ -> __IMPOSSIBLE__

mkPrimFun2 :: ( PrimType a, FromTerm a, ToTerm a
              , PrimType b, FromTerm b
              , PrimType c, ToTerm c ) =>
              (a -> b -> c) -> TCM PrimitiveImpl
mkPrimFun2 f = do
    toA   <- fromTerm
    fromA <- toTerm
    toB   <- fromTerm
    fromC <- toTerm
    t     <- primType f
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \ts ->
      case ts of
        [v,w] ->
          redBind (toA v)
              (\v' -> [v', notReduced w]) $ \x ->
          redBind (toB w)
              (\w' -> [ reduced $ notBlocked $ Arg (argInfo v) (fromA x)
                      , w']) $ \y ->
          redReturn $ fromC $ f x y
        _ -> __IMPOSSIBLE__

mkPrimFun4 :: ( PrimType a, FromTerm a, ToTerm a
              , PrimType b, FromTerm b, ToTerm b
              , PrimType c, FromTerm c, ToTerm c
              , PrimType d, FromTerm d
              , PrimType e, ToTerm e ) =>
              (a -> b -> c -> d -> e) -> TCM PrimitiveImpl
mkPrimFun4 f = do
    (toA, fromA) <- (,) <$> fromTerm <*> toTerm
    (toB, fromB) <- (,) <$> fromTerm <*> toTerm
    (toC, fromC) <- (,) <$> fromTerm <*> toTerm
    toD          <- fromTerm
    fromE        <- toTerm
    t <- primType f
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 4 $ \ts ->
      let argFrom fromX a x =
            reduced $ notBlocked $ Arg (argInfo a) (fromX x)
      in case ts of
        [a,b,c,d] ->
          redBind (toA a)
              (\a' -> a' : map notReduced [b,c,d]) $ \x ->
          redBind (toB b)
              (\b' -> [argFrom fromA a x, b', notReduced c, notReduced d]) $ \y ->
          redBind (toC c)
              (\c' -> [ argFrom fromA a x
                      , argFrom fromB b y
                      , c', notReduced d]) $ \z ->
          redBind (toD d)
              (\d' -> [ argFrom fromA a x
                      , argFrom fromB b y
                      , argFrom fromC c z
                      , d']) $ \w ->

          redReturn $ fromE $ f x y z w
        _ -> __IMPOSSIBLE__


---------------------------------------------------------------------------
-- * The actual primitive functions
---------------------------------------------------------------------------

type Op   a = a -> a -> a
type Fun  a = a -> a
type Rel  a = a -> a -> Bool
type Pred a = a -> Bool

primitiveFunctions :: Map String (TCM PrimitiveImpl)
primitiveFunctions = Map.fromList

  -- Ulf, 2015-10-28: Builtin integers now map to a datatype, and since you
  -- can define these functions (reasonably) efficiently using the primitive
  -- functions on natural numbers there's no need for them anymore. Keeping the
  -- show function around for convenience, and as a test case for a primitive
  -- function taking an integer.
  -- -- Integer functions
  -- [ "primIntegerPlus"     |-> mkPrimFun2 ((+)        :: Op Integer)
  -- , "primIntegerMinus"    |-> mkPrimFun2 ((-)        :: Op Integer)
  -- , "primIntegerTimes"    |-> mkPrimFun2 ((*)        :: Op Integer)
  -- , "primIntegerDiv"      |-> mkPrimFun2 (div        :: Op Integer)    -- partial
  -- , "primIntegerMod"      |-> mkPrimFun2 (mod        :: Op Integer)    -- partial
  -- , "primIntegerEquality" |-> mkPrimFun2 ((==)       :: Rel Integer)
  -- , "primIntegerLess"     |-> mkPrimFun2 ((<)        :: Rel Integer)
  -- , "primIntegerAbs"      |-> mkPrimFun1 (Nat . abs  :: Integer -> Nat)
  -- , "primNatToInteger"    |-> mkPrimFun1 (toInteger  :: Nat -> Integer)
  [ "primShowInteger"     |-> mkPrimFun1 (Str . show :: Integer -> Str)

  -- Natural number functions
  , "primNatPlus"         |-> mkPrimFun2 ((+)                     :: Op Nat)
  , "primNatMinus"        |-> mkPrimFun2 ((\x y -> max 0 (x - y)) :: Op Nat)
  , "primNatTimes"        |-> mkPrimFun2 ((*)                     :: Op Nat)
  , "primNatDivSucAux"    |-> mkPrimFun4 ((\k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Nat -> Nat -> Op Nat)
  , "primNatModSucAux"    |->
      let aux :: Nat -> Nat -> Op Nat
          aux k m n j | n > j     = mod (n - j - 1) (m + 1)
                      | otherwise = k + n
      in mkPrimFun4 aux
  , "primNatEquality"     |-> mkPrimFun2 ((==) :: Rel Nat)
  , "primNatLess"         |-> mkPrimFun2 ((<)  :: Rel Nat)
  , "primShowNat"         |-> mkPrimFun1 (Str . show :: Nat -> Str)

  -- Machine words
  , "primWord64ToNat"     |-> mkPrimFun1 (fromIntegral :: Word64 -> Nat)
  , "primWord64FromNat"   |-> mkPrimFun1 (fromIntegral :: Nat -> Word64)
  , "primWord64ToNatInjective" |-> primWord64ToNatInjective

  -- Level functions
  , "primLevelZero"       |-> mkPrimLevelZero
  , "primLevelSuc"        |-> mkPrimLevelSuc
  , "primLevelMax"        |-> mkPrimLevelMax

  -- Sorts
  , "primSetOmega"        |-> mkPrimSetOmega

  -- Floating point functions
  , "primNatToFloat"      |-> mkPrimFun1 (fromIntegral    :: Nat -> Double)
  , "primFloatPlus"       |-> mkPrimFun2 ((+)             :: Op Double)
  , "primFloatMinus"      |-> mkPrimFun2 ((-)             :: Op Double)
  , "primFloatTimes"      |-> mkPrimFun2 ((*)             :: Op Double)
  , "primFloatNegate"     |-> mkPrimFun1 (negate          :: Fun Double)
  , "primFloatDiv"        |-> mkPrimFun2 ((/)             :: Op Double)
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , "primFloatEquality"   |-> mkPrimFun2 (floatEq         :: Rel Double)
  , "primFloatLess"       |-> mkPrimFun2 (floatLt         :: Rel Double)
  , "primFloatNumericalEquality" |-> mkPrimFun2 ((==)     :: Rel Double)
  , "primFloatNumericalLess"     |-> mkPrimFun2 ((<)      :: Rel Double)
  , "primFloatSqrt"       |-> mkPrimFun1 (sqrt            :: Double -> Double)
  , "primRound"           |-> mkPrimFun1 (round   . normaliseNaN :: Double -> Integer)
  , "primFloor"           |-> mkPrimFun1 (floor   . normaliseNaN :: Double -> Integer)
  , "primCeiling"         |-> mkPrimFun1 (ceiling . normaliseNaN :: Double -> Integer)
  , "primExp"             |-> mkPrimFun1 (exp             :: Fun Double)
  , "primLog"             |-> mkPrimFun1 (log             :: Fun Double)
  , "primSin"             |-> mkPrimFun1 (sin             :: Fun Double)
  , "primCos"             |-> mkPrimFun1 (cos             :: Fun Double)
  , "primTan"             |-> mkPrimFun1 (tan             :: Fun Double)
  , "primASin"            |-> mkPrimFun1 (asin            :: Fun Double)
  , "primACos"            |-> mkPrimFun1 (acos            :: Fun Double)
  , "primATan"            |-> mkPrimFun1 (atan            :: Fun Double)
  , "primATan2"           |-> mkPrimFun2 (atan2           :: Op Double)
  , "primShowFloat"       |-> mkPrimFun1 (Str . show      :: Double -> Str)
  , "primFloatToWord64"   |-> mkPrimFun1 doubleToWord64
  , "primFloatToWord64Injective" |-> primFloatToWord64Injective

  -- Character functions
  , "primCharEquality"       |-> mkPrimFun2 ((==) :: Rel Char)
  , "primIsLower"            |-> mkPrimFun1 isLower
  , "primIsDigit"            |-> mkPrimFun1 isDigit
  , "primIsAlpha"            |-> mkPrimFun1 isAlpha
  , "primIsSpace"            |-> mkPrimFun1 isSpace
  , "primIsAscii"            |-> mkPrimFun1 isAscii
  , "primIsLatin1"           |-> mkPrimFun1 isLatin1
  , "primIsPrint"            |-> mkPrimFun1 isPrint
  , "primIsHexDigit"         |-> mkPrimFun1 isHexDigit
  , "primToUpper"            |-> mkPrimFun1 toUpper
  , "primToLower"            |-> mkPrimFun1 toLower
  , "primCharToNat"          |-> mkPrimFun1 (fromIntegral . fromEnum :: Char -> Nat)
  , "primCharToNatInjective" |-> primCharToNatInjective
  , "primNatToChar"          |-> mkPrimFun1 (toEnum . fromIntegral . (`mod` 0x110000)  :: Nat -> Char)
  , "primShowChar"           |-> mkPrimFun1 (Str . prettyShow . (LitChar noRange :: Char -> Literal))

  -- String functions
  , "primStringToList"          |-> mkPrimFun1 unStr
  , "primStringToListInjective" |-> primStringToListInjective
  , "primStringFromList"        |-> mkPrimFun1 Str
  , "primStringAppend"          |-> mkPrimFun2 (\s1 s2 -> Str $ unStr s1 ++ unStr s2)
  , "primStringEquality"        |-> mkPrimFun2 ((==) :: Rel Str)
  , "primShowString"            |-> mkPrimFun1 (Str . prettyShow . (LitString noRange :: String -> Literal) . unStr)

  -- Other stuff
  , "primEraseEquality"   |-> primEraseEquality
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , "primForce"           |-> primForce
  , "primForceLemma"      |-> primForceLemma
  , "primQNameEquality"   |-> mkPrimFun2 ((==) :: Rel QName)
  , "primQNameLess"       |-> mkPrimFun2 ((<) :: Rel QName)
  , "primShowQName"       |-> mkPrimFun1 (Str . prettyShow :: QName -> Str)
  , "primQNameFixity"     |-> mkPrimFun1 (nameFixity . qnameName)
  , "primQNameToWord64s"  |-> mkPrimFun1 ((\ (NameId x y) -> (x, y)) . nameId . qnameName
                                          :: QName -> (Word64, Word64))
  , "primQNameToWord64sInjective" |-> primQNameToWord64sInjective
  , "primMetaEquality"    |-> mkPrimFun2 ((==) :: Rel MetaId)
  , "primMetaLess"        |-> mkPrimFun2 ((<) :: Rel MetaId)
  , "primShowMeta"        |-> mkPrimFun1 (Str . prettyShow :: MetaId -> Str)
  , "primMetaToNat"       |-> mkPrimFun1 (fromIntegral . metaId :: MetaId -> Nat)
  , "primMetaToNatInjective" |-> primMetaToNatInjective
  , "primIMin"            |-> primIMin'
  , "primIMax"            |-> primIMax'
  , "primINeg"            |-> primINeg'
  , "primPOr"             |-> primPOr
  , "primComp"            |-> primComp
  , builtinTrans          |-> primTrans'
  , builtinHComp          |-> primHComp'
  , "primIdJ"             |-> primIdJ
  , "primPartial"         |-> primPartial'
  , "primPartialP"        |-> primPartialP'
  , builtinGlue           |-> primGlue'
  , builtin_glue          |-> prim_glue'
  , builtin_unglue        |-> prim_unglue'
  , builtinFaceForall     |-> primFaceForall'
  , "primDepIMin"         |-> primDepIMin'
  , "primIdFace"          |-> primIdFace'
  , "primIdPath"          |-> primIdPath'
  , builtinIdElim         |-> primIdElim'
  , builtinSubOut         |-> primSubOut'
  , builtin_glueU         |-> prim_glueU'
  , builtin_unglueU       |-> prim_unglueU'
  ]
  where
    (|->) = (,)
