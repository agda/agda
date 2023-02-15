
{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive
       ( module Agda.TypeChecking.Primitive.Base
       , module Agda.TypeChecking.Primitive.Cubical
       , module Agda.TypeChecking.Primitive
       ) where

import Data.Char
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word

import qualified Agda.Interaction.Options.Lenses as Lens

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level

import Agda.TypeChecking.Quote (quoteTermWithKit, quoteTypeWithKit, quoteDomWithKit, quotingKit)
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Primitive.Cubical.Base
import Agda.TypeChecking.Warnings

import Agda.Utils.Char
import Agda.Utils.Float
import Agda.Utils.List
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Size

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

instance Pretty Nat where
  pretty = pretty . toInteger

newtype Lvl = Lvl { unLvl :: Integer }
  deriving (Eq, Ord)

instance Pretty Lvl where
  pretty = pretty . unLvl

class PrimType a where
  primType :: a -> TCM Type

  -- This used to be a catch-all instance `PrimType a => PrimTerm a` which required UndecidableInstances.
  -- Now we declare the instances separately, but enforce the catch-all-ness with a superclass constraint on PrimTerm.
  default primType :: PrimTerm a => a -> TCM Type
  primType _ = el $ primTerm (undefined :: a)

class PrimType a => PrimTerm a where
  primTerm :: a -> TCM Term

instance (PrimType a, PrimType b) => PrimType (a -> b)
instance (PrimType a, PrimType b) => PrimTerm (a -> b) where
  primTerm _ = unEl <$> (primType (undefined :: a) --> primType (undefined :: b))

instance (PrimType a, PrimType b) => PrimType (a, b)
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

instance PrimType Integer
instance PrimTerm Integer where primTerm _ = primInteger

instance PrimType Word64
instance PrimTerm Word64  where primTerm _ = primWord64

instance PrimType Bool
instance PrimTerm Bool    where primTerm _ = primBool

instance PrimType Char
instance PrimTerm Char    where primTerm _ = primChar

instance PrimType Double
instance PrimTerm Double  where primTerm _ = primFloat

instance PrimType Text
instance PrimTerm Text    where primTerm _ = primString

instance PrimType Nat
instance PrimTerm Nat     where primTerm _ = primNat

instance PrimType Lvl
instance PrimTerm Lvl     where primTerm _ = primLevel

instance PrimType QName
instance PrimTerm QName   where primTerm _ = primQName

instance PrimType MetaId
instance PrimTerm MetaId  where primTerm _ = primAgdaMeta

instance PrimType Type
instance PrimTerm Type    where primTerm _ = primAgdaTerm

instance PrimType Fixity'
instance PrimTerm Fixity' where primTerm _ = primFixity

instance PrimTerm a => PrimType [a]
instance PrimTerm a => PrimTerm [a] where
  primTerm _ = list (primTerm (undefined :: a))

instance PrimTerm a => PrimType (Maybe a)
instance PrimTerm a => PrimTerm (Maybe a) where
  primTerm _ = tMaybe (primTerm (undefined :: a))

instance PrimTerm a => PrimType (IO a)
instance PrimTerm a => PrimTerm (IO a) where
  primTerm _ = io (primTerm (undefined :: a))

-- From Agda term to Haskell value

class ToTerm a where
  toTerm  :: TCM (a -> Term)
  toTermR :: TCM (a -> ReduceM Term)

  toTermR = (pure .) <$> toTerm

instance ToTerm Nat     where toTerm = return $ Lit . LitNat . toInteger
instance ToTerm Word64  where toTerm = return $ Lit . LitWord64
instance ToTerm Lvl     where toTerm = return $ Level . ClosedLevel . unLvl
instance ToTerm Double  where toTerm = return $ Lit . LitFloat
instance ToTerm Char    where toTerm = return $ Lit . LitChar
instance ToTerm Text    where toTerm = return $ Lit . LitString
instance ToTerm QName   where toTerm = return $ Lit . LitQName
instance ToTerm MetaId  where
  toTerm = do
    top <- fromMaybe __IMPOSSIBLE__ <$> currentTopLevelModule
    return $ Lit . LitMeta top

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
  toTermR = do quoteTermWithKit <$> quotingKit;

instance ToTerm (Dom Type) where
  toTerm  = do kit <- quotingKit; runReduceF (quoteDomWithKit kit)
  toTermR = do quoteDomWithKit <$> quotingKit

instance ToTerm Type where
  toTerm  = do kit <- quotingKit; runReduceF (quoteTypeWithKit kit)
  toTermR = quoteTypeWithKit <$> quotingKit

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

instance ToTerm a => ToTerm (Maybe a) where
  toTerm = do
    nothing <- primNothing
    just    <- primJust
    fromA   <- toTerm
    return $ maybe nothing (apply1 just . fromA)

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
  fromTerm = fromLiteral $ \case
    LitNat n -> Just $ fromInteger n
    _ -> Nothing

instance FromTerm Word64 where
  fromTerm = fromLiteral $ \ case
    LitWord64 n -> Just n
    _ -> Nothing

instance FromTerm Lvl where
  fromTerm = fromReducedTerm $ \case
    Level (ClosedLevel n) -> Just $ Lvl n
    _ -> Nothing

instance FromTerm Double where
  fromTerm = fromLiteral $ \case
    LitFloat x -> Just x
    _ -> Nothing

instance FromTerm Char where
  fromTerm = fromLiteral $ \case
    LitChar c -> Just c
    _ -> Nothing

instance FromTerm Text where
  fromTerm = fromLiteral $ \case
    LitString s -> Just s
    _ -> Nothing

instance FromTerm QName where
  fromTerm = fromLiteral $ \case
    LitQName x -> Just x
    _ -> Nothing

instance FromTerm MetaId where
  fromTerm = fromLiteral $ \case
    LitMeta _ x -> Just x
    _ -> Nothing

instance FromTerm Bool where
    fromTerm = do
        true  <- primTrue
        false <- primFalse
        fromReducedTerm $ \case
            t   | t =?= true  -> Just True
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
    nil   <- isCon <$> primNil
    cons  <- isCon <$> primCons
    toA   <- fromTerm
    mkList nil cons toA <$> toTerm
    where
      isCon (Lam _ b)   = isCon $ absBody b
      isCon (Con c _ _) = c
      isCon v           = __IMPOSSIBLE__

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

instance FromTerm a => FromTerm (Maybe a) where
  fromTerm = do
    nothing <- isCon <$> primNothing
    just    <- isCon <$> primJust
    toA     <- fromTerm
    return $ \ t -> do
      let arg = (<$ t)
      b <- reduceB' t
      let t = ignoreBlocking b
      case unArg t of
        Con c ci []
          | c == nothing -> return $ YesReduction NoSimplification Nothing
        Con c ci es
          | c == just, Just [x] <- allApplyElims es ->
            redBind (toA x)
              (\ x' -> notReduced $ arg $ Con c ci [Apply (ignoreReduced x')])
              (redReturn . Just)
        _ -> return $ NoReduction (reduced b)

    where
      isCon (Lam _ b)   = isCon $ absBody b
      isCon (Con c _ _) = c
      isCon v           = __IMPOSSIBLE__


fromReducedTerm :: (Term -> Maybe a) -> TCM (FromTermFunction a)
fromReducedTerm f = return $ \t -> do
    b <- reduceB' t
    case f $ unArg (ignoreBlocking b) of
        Just x  -> return $ YesReduction NoSimplification x
        Nothing -> return $ NoReduction (reduced b)

fromLiteral :: (Literal -> Maybe a) -> TCM (FromTermFunction a)
fromLiteral f = fromReducedTerm $ \case
    Lit lit -> f lit
    _       -> Nothing

-- | @mkPrimInjective@ takes two Set0 @a@ and @b@ and a function @f@ of type
--   @a -> b@ and outputs a primitive internalizing the fact that @f@ is injective.
mkPrimInjective :: Type -> Type -> QName -> TCM PrimitiveImpl
mkPrimInjective a b qn = do
  -- Define the type
  eqName <- primEqualityName
  let lvl0     = ClosedLevel 0
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
    reduce' eq >>= \case
      Con{} -> redReturn $ refl t
      _     -> return $ NoReduction $ map notReduced ts

-- | Converts 'MetaId's to natural numbers.

metaToNat :: MetaId -> Nat
metaToNat m =
  fromIntegral (moduleNameHash $ metaModule m) * 2^64 +
  fromIntegral (metaId m)

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
  string <- primType (undefined :: Text)
  chars  <- primType (undefined :: String)
  toList <- primFunName <$> getPrimitive "primStringToList"
  mkPrimInjective string chars toList

primStringFromListInjective :: TCM PrimitiveImpl
primStringFromListInjective = do
  chars  <- primType (undefined :: String)
  string <- primType (undefined :: Text)
  fromList <- primFunName <$> getPrimitive "primStringFromList"
  mkPrimInjective chars string fromList

primWord64ToNatInjective :: TCM PrimitiveImpl
primWord64ToNatInjective =  do
  word  <- primType (undefined :: Word64)
  nat   <- primType (undefined :: Nat)
  toNat <- primFunName <$> getPrimitive "primWord64ToNat"
  mkPrimInjective word nat toNat

primFloatToWord64Injective :: TCM PrimitiveImpl
primFloatToWord64Injective = do
  float  <- primType (undefined :: Double)
  mword  <- primType (undefined :: Maybe Word64)
  toWord <- primFunName <$> getPrimitive "primFloatToWord64"
  mkPrimInjective float mword toWord

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
                Var{}      -> return False
                MetaV{}    -> __IMPOSSIBLE__
                Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s
        ifM (isWHNF u)
            (redReturn $ ret (unArg f) (ignoreBlocking u))
            (return $ NoReduction $ map notReduced [a, b, s, t] ++ [reduced u, notReduced f])
      _ -> __IMPOSSIBLE__

primForce :: TCM PrimitiveImpl
primForce = do
  let varEl s a = El (varSort s) <$> a
      varT s a  = varEl s (varM a)
  genPrimForce (nPi "x" (varT 3 1) $
                nPi "y" (varT 4 2) (varEl 4 $ varM 2 <@> varM 0) -->
                varEl 3 (varM 1 <@> varM 0)) $
    \ f u -> apply f [u]

primForceLemma :: TCM PrimitiveImpl
primForceLemma = do
  let varEl s a = El (varSort s) <$> a
      varT s a  = varEl s (varM a)
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
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Level $ ClosedLevel 0

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
    a' <- levelView' $ unArg a
    b' <- levelView' $ unArg b
    redReturn $ Level $ levelLub a' b'

mkPrimSetOmega :: IsFibrant -> TCM PrimitiveImpl
mkPrimSetOmega f = do
  let t = sort $ Inf f 1
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Sort $ Inf f 0

primLockUniv' :: TCM PrimitiveImpl
primLockUniv' = do
  let t = sort $ Type $ levelSuc $ Max 0 []
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Sort LockUniv

primLevelUniv' :: TCM PrimitiveImpl
primLevelUniv' = do
  let t = sort $ Type $ ClosedLevel 1
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Sort $ LevelUniv

-- mkPrimStrictSet :: TCM PrimitiveImpl
-- mkPrimStrictSet = do
--   t <- nPi "ℓ" (el primLevel) (pure $ sort $ SSet $ Max 0 [Plus 1 $ var 0])
--   return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ ~[a] -> do
--     l <- levelView' $ unArg a
--     redReturn $ Sort $ SSet l

mkPrimFun1TCM :: (FromTerm a, ToTerm b) =>
                 TCM Type -> (a -> ReduceM b) -> TCM PrimitiveImpl
mkPrimFun1TCM mt f = do
    toA   <- fromTerm
    fromB <- toTermR
    t     <- mt
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ts ->
      case ts of
        [v] ->
          redBind (toA v) singleton $ \ x -> do
            b <- fromB =<< f x
            case allMetas Set.singleton b of
              ms | Set.null ms -> redReturn b
                 | otherwise   -> return $ NoReduction [reduced (Blocked (unblockOnAllMetas ms) v)]
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

mkPrimFun3 :: ( PrimType a, FromTerm a, ToTerm a
              , PrimType b, FromTerm b, ToTerm b
              , PrimType c, FromTerm c
              , PrimType d, ToTerm d ) =>
              (a -> b -> c -> d) -> TCM PrimitiveImpl
mkPrimFun3 f = do
    (toA, fromA) <- (,) <$> fromTerm <*> toTerm
    (toB, fromB) <- (,) <$> fromTerm <*> toTerm
    toC          <- fromTerm
    fromD        <- toTerm
    t <- primType f
    return $ PrimImpl t $ primFun __IMPOSSIBLE__ 3 $ \ts ->
      let argFrom fromX a x =
            reduced $ notBlocked $ Arg (argInfo a) (fromX x)
      in case ts of
        [a,b,c] ->
          redBind (toA a)
              (\a' -> [a', notReduced b, notReduced c]) $ \x ->
          redBind (toB b)
              (\b' -> [argFrom fromA a x, b', notReduced c]) $ \y ->
          redBind (toC c)
              (\c' -> [ argFrom fromA a x, argFrom fromB b y, c']) $ \z ->
          redReturn $ fromD $ f x y z
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
primitiveFunctions = localTCStateSavingWarnings <$> Map.fromListWith __IMPOSSIBLE__
  -- Issue #4375          ^^^^^^^^^^^^^^^^^^^^^^^^^^
  --   Without this the next fresh checkpoint id gets changed building the primitive functions. This
  --   is bad for caching since it happens when scope checking import declarations (rebinding
  --   primitives). During type checking, the caching machinery might then load a cached state with
  --   out-of-date checkpoint ids. Make sure to preserve warnings though, since they include things
  --   like using unsafe things primitives with `--safe`.

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
  [ "primShowInteger"     |-> mkPrimFun1 (T.pack . prettyShow :: Integer -> Text)

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
  , "primShowNat"         |-> mkPrimFun1 (T.pack . prettyShow :: Nat -> Text)

  -- Machine words
  , "primWord64ToNat"     |-> mkPrimFun1 (fromIntegral :: Word64 -> Nat)
  , "primWord64FromNat"   |-> mkPrimFun1 (fromIntegral :: Nat -> Word64)
  , "primWord64ToNatInjective" |-> primWord64ToNatInjective

  -- Level functions
  , "primLevelZero"       |-> mkPrimLevelZero
  , "primLevelSuc"        |-> mkPrimLevelSuc
  , "primLevelMax"        |-> mkPrimLevelMax

  -- Sorts
  , "primSetOmega"        |-> mkPrimSetOmega IsFibrant
  , "primStrictSetOmega"  |-> mkPrimSetOmega IsStrict

  -- Floating point functions
  --
  -- Wen, 2020-08-26: Primitives which convert from Float into other, more
  -- well-behaved numeric types should check for unrepresentable values, e.g.,
  -- NaN and the infinities, and return `nothing` if those are encountered, to
  -- ensure that the returned numbers are sensible. That means `primFloatRound`,
  -- `primFloatFloor`, `primFloatCeiling`, and `primFloatDecode`. The conversion
  -- `primFloatRatio` represents NaN as (0,0), and the infinities as (±1,0).
  --
  , "primFloatEquality"          |-> mkPrimFun2 doubleEq
  , "primFloatInequality"        |-> mkPrimFun2 doubleLe
  , "primFloatLess"              |-> mkPrimFun2 doubleLt
  , "primFloatIsInfinite"        |-> mkPrimFun1 (isInfinite :: Double -> Bool)
  , "primFloatIsNaN"             |-> mkPrimFun1 (isNaN :: Double -> Bool)
  , "primFloatIsNegativeZero"    |-> mkPrimFun1 (isNegativeZero :: Double -> Bool)
  , "primFloatIsSafeInteger"     |-> mkPrimFun1 isSafeInteger
  , "primFloatToWord64"          |-> mkPrimFun1 doubleToWord64
  , "primFloatToWord64Injective" |-> primFloatToWord64Injective
  , "primNatToFloat"             |-> mkPrimFun1 (intToDouble :: Nat -> Double)
  , "primIntToFloat"             |-> mkPrimFun1 (intToDouble :: Integer -> Double)
  , "primFloatRound"             |-> mkPrimFun1 doubleRound
  , "primFloatFloor"             |-> mkPrimFun1 doubleFloor
  , "primFloatCeiling"           |-> mkPrimFun1 doubleCeiling
  , "primFloatToRatio"           |-> mkPrimFun1 doubleToRatio
  , "primRatioToFloat"           |-> mkPrimFun2 ratioToDouble
  , "primFloatDecode"            |-> mkPrimFun1 doubleDecode
  , "primFloatEncode"            |-> mkPrimFun2 doubleEncode
  , "primShowFloat"              |-> mkPrimFun1 (T.pack . show :: Double -> Text)
  , "primFloatPlus"              |-> mkPrimFun2 doublePlus
  , "primFloatMinus"             |-> mkPrimFun2 doubleMinus
  , "primFloatTimes"             |-> mkPrimFun2 doubleTimes
  , "primFloatNegate"            |-> mkPrimFun1 doubleNegate
  , "primFloatDiv"               |-> mkPrimFun2 doubleDiv
  , "primFloatPow"               |-> mkPrimFun2 doublePow
  , "primFloatSqrt"              |-> mkPrimFun1 doubleSqrt
  , "primFloatExp"               |-> mkPrimFun1 doubleExp
  , "primFloatLog"               |-> mkPrimFun1 doubleLog
  , "primFloatSin"               |-> mkPrimFun1 doubleSin
  , "primFloatCos"               |-> mkPrimFun1 doubleCos
  , "primFloatTan"               |-> mkPrimFun1 doubleTan
  , "primFloatASin"              |-> mkPrimFun1 doubleASin
  , "primFloatACos"              |-> mkPrimFun1 doubleACos
  , "primFloatATan"              |-> mkPrimFun1 doubleATan
  , "primFloatATan2"             |-> mkPrimFun2 doubleATan2
  , "primFloatSinh"              |-> mkPrimFun1 doubleSinh
  , "primFloatCosh"              |-> mkPrimFun1 doubleCosh
  , "primFloatTanh"              |-> mkPrimFun1 doubleTanh
  , "primFloatASinh"             |-> mkPrimFun1 doubleASinh
  , "primFloatACosh"             |-> mkPrimFun1 doubleCosh
  , "primFloatATanh"             |-> mkPrimFun1 doubleTanh

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
  , "primNatToChar"          |-> mkPrimFun1 (integerToChar . unNat)
  , "primShowChar"           |-> mkPrimFun1 (T.pack . prettyShow . LitChar)

  -- String functions
  , "primStringToList"            |-> mkPrimFun1 T.unpack
  , "primStringToListInjective"   |-> primStringToListInjective
  , "primStringFromList"          |-> mkPrimFun1 T.pack
  , "primStringFromListInjective" |-> primStringFromListInjective
  , "primStringAppend"            |-> mkPrimFun2 (T.append :: Text -> Text -> Text)
  , "primStringEquality"          |-> mkPrimFun2 ((==) :: Rel Text)
  , "primShowString"              |-> mkPrimFun1 (T.pack . prettyShow . LitString)
  , "primStringUncons"            |-> mkPrimFun1 T.uncons

  -- Other stuff
  , "primEraseEquality"   |-> primEraseEquality
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , "primForce"           |-> primForce
  , "primForceLemma"      |-> primForceLemma
  , "primQNameEquality"   |-> mkPrimFun2 ((==) :: Rel QName)
  , "primQNameLess"       |-> mkPrimFun2 ((<) :: Rel QName)
  , "primShowQName"       |-> mkPrimFun1 (T.pack . prettyShow :: QName -> Text)
  , "primQNameFixity"     |-> mkPrimFun1 (nameFixity . qnameName)
  , "primQNameToWord64s"  |-> mkPrimFun1 ((\ (NameId x (ModuleNameHash y)) -> (x, y)) . nameId . qnameName
                                          :: QName -> (Word64, Word64))
  , "primQNameToWord64sInjective" |-> primQNameToWord64sInjective
  , "primMetaEquality"    |-> mkPrimFun2 ((==) :: Rel MetaId)
  , "primMetaLess"        |-> mkPrimFun2 ((<) :: Rel MetaId)
  , "primShowMeta"        |-> mkPrimFun1 (T.pack . prettyShow :: MetaId -> Text)
  , "primMetaToNat"       |-> mkPrimFun1 metaToNat
  , "primMetaToNatInjective" |-> primMetaToNatInjective
  , "primIMin"            |-> primIMin'
  , "primIMax"            |-> primIMax'
  , "primINeg"            |-> primINeg'
  , "primPOr"             |-> primPOr
  , "primComp"            |-> primComp
  , builtinTrans          |-> primTrans'
  , builtinHComp          |-> primHComp'
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
  , builtinConId          |-> primConId'
  , builtin_glueU         |-> prim_glueU'
  , builtin_unglueU       |-> prim_unglueU'
  , builtinLockUniv       |-> primLockUniv'
  , builtinLevelUniv      |-> primLevelUniv'
  ]
  where
    (|->) = (,)
