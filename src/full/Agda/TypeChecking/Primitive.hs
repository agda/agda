{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}

-- ASR (2017-04-10). TODO: Is this option required by the final
-- version of GHC 8.2.1 (it was required by the RC 1)?
#if __GLASGOW_HASKELL__ >= 802
{-# OPTIONS -Wno-simplifiable-class-constraints #-}
#endif

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive where

import Control.Monad
import Control.Monad.Reader (asks)
import Control.Monad.Trans (lift)

import Data.Char
import Data.Either (partitionEithers)
import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Traversable (traverse)
import Data.Monoid (mempty)
import Data.Word

import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Fixity

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import qualified Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Level
import Agda.TypeChecking.Quote (QuotingKit, quoteTermWithKit, quoteTypeWithKit, quoteClauseWithKit, quotingKit)
import Agda.TypeChecking.Pretty ()  -- instances only
import Agda.TypeChecking.Names
import Agda.TypeChecking.Warnings

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty, prettyShow)
import Agda.Utils.Size
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.Tuple
import Agda.Utils.Float

#include "undefined.h"
import Agda.Utils.Impossible
import Debug.Trace

------------------------------------------------------------------------
-- * Builtin Sigma
------------------------------------------------------------------------

data SigmaKit = SigmaKit
  { sigmaName :: QName
  , sigmaCon  :: ConHead
  , sigmaFst  :: QName
  , sigmaSnd  :: QName
  }
  deriving (Eq,Show)

getSigmaKit :: (HasBuiltins m, HasConstInfo m) => m (Maybe SigmaKit)
getSigmaKit = do
  ms <- getBuiltinName' builtinSigma
  case ms of
    Nothing -> return Nothing
    Just sigma -> do
      def <- theDef <$> getConstInfo sigma
      case def of
        Record { recFields = [fst,snd], recConHead = con } -> do
          return . Just $ SigmaKit
            { sigmaName = sigma
            , sigmaCon  = con
            , sigmaFst  = unArg fst
            , sigmaSnd  = unArg snd
            }
        _ -> __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Primitive functions
---------------------------------------------------------------------------

data PrimitiveImpl = PrimImpl Type PrimFun

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

instance ToTerm PrecedenceLevel where
  toTerm = do
    (iToTm :: Integer -> Term) <- toTerm
    related   <- primPrecRelated
    unrelated <- primPrecUnrelated
    return $ \ p ->
      case p of
        Unrelated -> unrelated
        Related n -> related `apply` [defaultArg $ iToTm n]

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

-- | Conceptually: @redBind m f k = either (return . Left . f) k =<< m@
redBind :: ReduceM (Reduced a a') -> (a -> b) ->
           (a' -> ReduceM (Reduced b b')) -> ReduceM (Reduced b b')
redBind ma f k = do
    r <- ma
    case r of
        NoReduction x    -> return $ NoReduction $ f x
        YesReduction _ y -> k y

redReturn :: a -> ReduceM (Reduced a' a)
redReturn = return . YesReduction YesSimplification

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

requireCubical :: TCM ()
requireCubical = do
  cubical <- optCubical <$> pragmaOptions
  unless cubical $
    typeError $ GenericError "Missing option --cubical"

primINeg' :: TCM PrimitiveImpl
primINeg' = do
  requireCubical
  t <- elInf primInterval --> elInf primInterval
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ ts -> do
    case ts of
     [x] -> do
       unview <- intervalUnview'
       view <- intervalView'
       sx <- reduceB' x
       ix <- intervalView (unArg $ ignoreBlocking sx)
       let
         ineg :: Arg Term -> Arg Term
         ineg = fmap (unview . f . view)
         f ix = case ix of
           IZero -> IOne
           IOne  -> IZero
           IMin x y -> IMax (ineg x) (ineg y)
           IMax x y -> IMin (ineg x) (ineg y)
           INeg x -> OTerm (unArg x)
           OTerm t -> INeg (Arg defaultArgInfo t)
       case ix of
        OTerm t -> return $ NoReduction [reduced sx]
        _       -> redReturn (unview $ f ix)
     _ -> __IMPOSSIBLE__

primDepIMin' :: TCM PrimitiveImpl
primDepIMin' = do
  requireCubical
  t <- runNamesT [] $
       nPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       (pPi' "o" φ $ \ o -> elInf $ cl primInterval) --> elInf (cl primInterval)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \ ts -> do
    case ts of
      [x,y] -> do
        sx <- reduceB' x
        ix <- intervalView (unArg $ ignoreBlocking sx)
        itisone <- getTerm "primDepIMin" builtinItIsOne
        case ix of
          IZero -> redReturn =<< intervalUnview IZero
          IOne  -> redReturn =<< (pure (unArg y) <@> pure itisone)
          _     -> do
            sy <- reduceB' y
            iy <- intervalView =<< reduce' =<< (pure (unArg $ ignoreBlocking sy) <@> pure itisone)
            case iy of
              IZero -> redReturn =<< intervalUnview IZero
              IOne  -> redReturn (unArg $ ignoreBlocking sx)
              _     -> return $ NoReduction [reduced sx, reduced sy]
      _      -> __IMPOSSIBLE__

primIBin :: IntervalView -> IntervalView -> TCM PrimitiveImpl
primIBin unit absorber = do
  requireCubical
  t <- elInf primInterval --> elInf primInterval --> elInf primInterval
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \ ts -> do
    case ts of
     [x,y] -> do
       sx <- reduceB' x
       ix <- intervalView (unArg $ ignoreBlocking sx)
       case ix of
         ix | ix ==% absorber -> redReturn =<< intervalUnview absorber
         ix | ix ==% unit     -> return $ YesReduction YesSimplification (unArg y)
         _     -> do
           sy <- reduceB' y
           iy <- intervalView (unArg $ ignoreBlocking sy)
           case iy of
            iy | iy ==% absorber -> redReturn =<< intervalUnview absorber
            iy | iy ==% unit     -> return $ YesReduction YesSimplification (unArg x)
            _                   -> return $ NoReduction [reduced sx,reduced sy]
     _ -> __IMPOSSIBLE__
  where
    (==%) IZero IZero = True
    (==%) IOne IOne = True
    (==%) _ _ = False


primIMin' :: TCM PrimitiveImpl
primIMin' = primIBin IOne IZero

primIMax' :: TCM PrimitiveImpl
primIMax' = primIBin IZero IOne

imax :: HasBuiltins m => m Term -> m Term -> m Term
imax x y = do
  x' <- x
  y' <- y
  intervalUnview (IMax (argN x') (argN y'))

imin :: HasBuiltins m => m Term -> m Term -> m Term
imin x y = do
  x' <- x
  y' <- y
  intervalUnview (IMin (argN x') (argN y'))

-- ∀ {a}{c}{A : Set a}{x : A}(C : ∀ y → Id x y → Set c) → C x (conid i1 (\ i → x)) → ∀ {y} (p : Id x y) → C y p
primIdJ :: TCM PrimitiveImpl
primIdJ = do
  requireCubical
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "c" (el $ cl primLevel) $ \ c ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       nPi' "C" (nPi' "y" (el' a bA) $ \ y ->
                 (el' a $ cl primId <#> a <#> bA <@> x <@> y) --> (sort . tmSort <$> c)) $ \ bC ->
       (el' c $ bC <@> x <@>
            (cl primConId <#> a <#> bA <#> x <#> x <@> cl primIOne
                       <@> lam "i" (\ _ -> x))) -->
       (hPi' "y" (el' a bA) $ \ y ->
        nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
        el' c $ bC <@> y <@> p)
  conidn <- getBuiltinName builtinConId
  conid  <- primConId
  -- TODO make a kit
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ ts -> do
    unview <- intervalUnview'
    let imax x y = do x' <- x; y' <- y; pure $ unview (IMax (argN x') (argN y'))
        imin x y = do x' <- x; y' <- y; pure $ unview (IMin (argN x') (argN y'))
        ineg x = unview . INeg . argN <$> x
    mcomp <- getTerm' "primComp"
    case ts of
     [la,lc,a,x,c,d,y,eq] -> do
       seq    <- reduceB' eq
       case unArg $ ignoreBlocking $ seq of
         (Def q [Apply la,Apply a,Apply x,Apply y,Apply phi,Apply p])
           | Just q == conidn, Just comp <- mcomp -> do
          redReturn $ runNames [] $ do
             [lc,c,d,la,a,x,y,phi,p] <- mapM (open . unArg) [lc,c,d,la,a,x,y,phi,p]
             let w i = do
                   [x,y,p,i] <- sequence [x,y,p,i]
                   pure $ p `applyE` [IApply x y i]
             pure comp <#> (lam "i" $ \ _ -> lc)
                       <@> (lam "i" $ \ i ->
                              c <@> (w i)
                                <@> (pure conid <#> la <#> a <#> x <#> (w i)
                                                <@> (phi `imax` ineg i)
                                                <@> (lam "j" $ \ j -> w $ imin i j)))
                       <@> phi
                       <@> (lam "i" $ \ _ -> nolam <$> d) -- TODO block
                       <@> d
         _ -> return $ NoReduction $ map notReduced [la,lc,a,x,c,d,y] ++ [reduced seq]
     _ -> __IMPOSSIBLE__

primIdElim' :: TCM PrimitiveImpl
primIdElim' = do
  requireCubical
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "c" (el $ cl primLevel) $ \ c ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       nPi' "C" (nPi' "y" (el' a bA) $ \ y ->
                 (el' a $ cl primId <#> a <#> bA <@> x <@> y) --> (sort . tmSort <$> c)) $ \ bC ->
       (nPi' "φ" (elInf $ cl primInterval) $ \ phi ->
        nPi' "y" (elInf $ cl primSub <#> a <@> bA <@> phi <@> (lam "o" $ const x)) $ \ y ->
        let pathxy = (cl primPath <#> a <@> bA <@> x <@> oucy)
            oucy = (cl primSubOut <#> a <#> bA <#> phi <#> (lam "o" $ const x) <@> y)
            reflx = (lam "o" $ \ _ -> lam "i" $ \ _ -> x) -- TODO Andrea, should block on o
        in
        nPi' "w" (elInf $ cl primSub <#> a <@> pathxy <@> phi <@> reflx) $ \ w ->
        let oucw = (cl primSubOut <#> a <#> pathxy <#> phi <#> reflx <@> w) in
        el' c $ bC <@> oucy <@> (cl primConId <#> a <#> bA <#> x <#> oucy <@> phi <@> oucw))
       -->
       (hPi' "y" (el' a bA) $ \ y ->
        nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
        el' c $ bC <@> y <@> p)
  conid <- primConId
  sin <- primSubIn
  path <- primPath
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ ts -> do
    case ts of
      [a,c,bA,x,bC,f,y,p] -> do
        sp <- reduceB' p
        case unArg $ ignoreBlocking sp of
          Def q [Apply _a, Apply _bA, Apply _x, Apply _y, Apply phi , Apply w] -> do
            y' <- return $ sin `apply` [a,bA                            ,phi,argN $ unArg y]
            w' <- return $ sin `apply` [a,argN $ path `apply` [a,bA,x,y],phi,argN $ unArg w]
            redReturn $ unArg f `apply` [phi, defaultArg y', defaultArg w']
          _ -> return $ NoReduction $ map notReduced [a,c,bA,x,bC,f,y] ++ [reduced sp]
      _ -> __IMPOSSIBLE__


primPOr :: TCM PrimitiveImpl
primPOr = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel)    $ \ a  ->
          nPi' "i" (elInf $ cl primInterval) $ \ i  ->
          nPi' "j" (elInf $ cl primInterval) $ \ j  ->
          hPi' "A" (pPi' "o" (imax i j) $ \o -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          ((pPi' "i1" i $ \ i1 -> el' a $ bA <..> (cl primIsOne1 <@> i <@> j <@> i1))) -->
          ((pPi' "j1" j $ \ j1 -> el' a $ bA <..> (cl primIsOne2 <@> i <@> j <@> j1))) -->
          (pPi' "o" (imax i j) $ \ o -> el' a $ bA <..> o)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts -> do
    case ts of
     [l,i,j,a,u,v] -> do
       si <- reduceB' i
       vi <- intervalView $ unArg $ ignoreBlocking si
       case vi of
        IOne -> redReturn (unArg u)
        IZero -> redReturn (unArg v)
        _ -> do
          sj <- reduceB' j
          vj <- intervalView $ unArg $ ignoreBlocking sj
          case vj of
            IOne -> redReturn (unArg v)
            IZero -> redReturn (unArg u)
            _ -> return $ NoReduction [notReduced l,reduced si,reduced sj,notReduced a,notReduced u,notReduced v]


     _ -> __IMPOSSIBLE__

primPartial' :: TCM PrimitiveImpl
primPartial' = do
  requireCubical
  t <- runNamesT [] $
       (hPi' "a" (el $ cl primLevel) $ \ a ->
        nPi' "φ" (elInf (cl primInterval)) $ \ _ ->
        nPi' "A" (sort . tmSort <$> a) $ \ bA ->
        return (sort $ Inf))
  isOne <- primIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
      [l,phi,a] -> do
          (El s (Pi d b)) <- runNamesT [] $ do
                             [l,a,phi] <- mapM (open . unArg) [l,a,phi]
                             (elInf $ pure isOne <@> phi) --> el' l a
          redReturn $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      _ -> __IMPOSSIBLE__

primPartialP' :: TCM PrimitiveImpl
primPartialP' = do
  requireCubical
  t <- runNamesT [] $
       (hPi' "a" (el $ cl primLevel) $ \ a ->
        nPi' "φ" (elInf (cl primInterval)) $ \ phi ->
        nPi' "A" (pPi' "o" phi $ \ _ -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
        return (sort $ Inf))
  let toFinitePi :: Type -> Term
      toFinitePi (El _ (Pi d b)) = Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      toFinitePi _               = __IMPOSSIBLE__
  v <- runNamesT [] $
        lam "a" $ \ l ->
        lam "φ" $ \ phi ->
        lam "A" $ \ a ->
        toFinitePi <$> nPi' "p" (elInf $ cl primIsOne <@> phi) (\ p -> el' l (a <@> p))
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v

primSubOut' :: TCM PrimitiveImpl
primSubOut' = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          hPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          hPi' "u" (elInf $ cl primPartial <#> a <@> phi <@> bA) $ \ u ->
          elInf (cl primSub <#> a <@> bA <@> phi <@> u) --> el' (Sort . tmSort <$> a) bA
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [a,bA,phi,u,x] -> do
        view <- intervalView'
        sphi <- reduceB' phi
        case view $ unArg $ ignoreBlocking sphi of
          IOne -> redReturn =<< (return (unArg u) <..> (getTerm builtinSubOut builtinItIsOne))
          _ -> do
            sx <- reduceB' x
            mSubIn <- getBuiltinName' builtinSubIn
            case unArg $ ignoreBlocking $ sx of
              Def q [_,_,_, Apply t] | Just q == mSubIn -> redReturn (unArg t)
              _ -> return $ NoReduction $ map notReduced [a,bA] ++ [reduced sphi, notReduced u, reduced sx]
      _ -> __IMPOSSIBLE__

primIdFace' :: TCM PrimitiveImpl
primIdFace' = do
  requireCubical
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       (el' a $ cl primId <#> a <#> bA <@> x <@> y)
       --> elInf (cl primInterval)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        case unArg (ignoreBlocking st) of
          Def q [_,_,_,_, Apply phi,_] | Just q == mConId -> redReturn (unArg phi)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__

primIdPath' :: TCM PrimitiveImpl
primIdPath' = do
  requireCubical
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       (el' a $ cl primId <#> a <#> bA <@> x <@> y)
       --> (el' a $ cl primPath <#> a <#> bA <@> x <@> y)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        case unArg (ignoreBlocking st) of
          Def q [_,_,_,_,_,Apply w] | Just q == mConId -> redReturn (unArg w)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__


primTrans' :: TCM PrimitiveImpl
primTrans' = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (elInf (cl primInterval) --> (el $ cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" (elInf (cl primInterval)) $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          nPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ ts nelims -> do
    primTransHComp DoTransp ts nelims

primHComp' :: TCM PrimitiveImpl
primHComp' = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (sort . tmSort <$> a) $ \ bA ->
          hPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          (nPi' "i" (elInf $ cl primInterval) $ \ i -> pPi' "o" phi $ \ _ -> el' a bA) -->
          (el' a bA --> el' a bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    primTransHComp DoHComp ts nelims

data TranspOrHComp = DoTransp | DoHComp deriving (Eq,Show)

cmdToName :: TranspOrHComp -> String
cmdToName DoTransp = builtinTrans
cmdToName DoHComp  = builtinHComp

data FamilyOrNot a = IsFam {famThing :: a} | IsNot {famThing :: a} deriving (Eq,Show,Functor,Foldable,Traversable)

instance Reduce a => Reduce (FamilyOrNot a) where
  reduceB' x = traverse id <$> traverse reduceB' x
  reduce' x = traverse reduce' x

primTransHComp :: TranspOrHComp -> [Arg Term] -> Int -> ReduceM (Reduced MaybeReducedArgs Term)
primTransHComp cmd ts nelims = do
  (l,bA,phi,u,u0) <- case (cmd,ts) of
        (DoTransp, [l,bA,phi,  u0]) -> do
          -- u <- runNamesT [] $ do
          --       u0 <- open $ unArg u0
          --       defaultArg <$> (ilam "o" $ \ _ -> u0)
          return $ (IsFam l,IsFam bA,phi,Nothing,u0)
        (DoHComp, [l,bA,phi,u,u0]) -> do
          -- [l,bA] <- runNamesT [] $ do
          --   forM [l,bA] $ \ a -> do
          --     let info = argInfo a
          --     a <- open $ unArg a
          --     Arg info <$> (lam "i" $ \ _ -> a)
          return $ (IsNot l,IsNot bA,phi,Just u,u0)
        _                          -> __IMPOSSIBLE__
  sphi <- reduceB' phi
  vphi <- intervalView $ unArg $ ignoreBlocking sphi
  let clP s = getTerm (cmdToName cmd) s

  -- WORK
  case vphi of
     IOne -> redReturn =<< case u of
                            -- cmd == DoComp
                            Just u -> runNamesT [] $ do
                                       u <- open (unArg u)
                                       u <@> clP builtinIOne <..> clP builtinItIsOne
                            -- cmd == DoTransp
                            Nothing -> return $ unArg u0
     _    -> do
       let fallback' sc = do
             u' <- case u of
                            -- cmd == DoComp
                     Just u ->
                              (:[]) <$> case vphi of
                                          IZero -> fmap (reduced . notBlocked . argN) . runNamesT [] $ do
                                            [l,c] <- mapM (open . unArg) [famThing l, ignoreBlocking sc]
                                            lam "i" $ \ i -> clP builtinIsOneEmpty <#> l
                                                                   <#> (ilam "o" $ \ _ -> c)
                                          _     -> return (notReduced u)
                            -- cmd == DoTransp
                     Nothing -> return []
             return $ NoReduction $ [notReduced (famThing l), reduced sc, reduced sphi] ++ u' ++ [notReduced u0]
       sbA <- reduceB' bA
       t <- case unArg <$> ignoreBlocking sbA of
              IsFam (Lam _info t) -> Just . fmap IsFam <$> reduceB' (absBody t)
              IsFam _             -> return Nothing
              IsNot t             -> return . Just . fmap IsNot $ (t <$ sbA)
       case t of
         Nothing -> fallback' (famThing <$> sbA)
         Just st  -> do
               let
                   fallback = fallback' (fmap famThing $ st *> sbA)
                   t = ignoreBlocking st
               mGlue <- getPrimitiveName' builtinGlue
               mId   <- getBuiltinName' builtinId
               pathV <- pathView'
               case famThing t of
                 MetaV m _ -> fallback' (fmap famThing $ Blocked m () *> sbA)
                 -- absName t instead of "i"
                 Pi a b | nelims > 0  -> redReturn =<< compPi cmd "i" ((a,b) <$ t) (ignoreBlocking sphi) u u0
                        | otherwise -> fallback

                 Sort (Type l) -> compSort cmd fallback phi u u0 (l <$ t)

                 Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
                   compGlue cmd phi u u0 ((la, lb, bA, phi', bT, e) <$ t)

                 -- Path/PathP
                 d | PathType _ _ _ bA x y <- pathV (El __DUMMY_SORT__ d) -> do
                   if nelims > 0 then compPathP cmd sphi u u0 l ((bA, x, y) <$ t) else fallback

                 Def q [Apply _ , Apply bA , Apply x , Apply y] | Just q == mId -> do
                   maybe fallback return =<< compId cmd sphi u u0 l ((bA, x, y) <$ t)

                 Def q es -> do
                   info <- getConstInfo q
                   let   lam_i = Lam defaultArgInfo . Abs "i"

                   case theDef info of
                     r@Record{recComp = kit} | nelims > 0, Just as <- allApplyElims es, DoTransp <- cmd, Just transpR <- nameOfTransp kit
                                -> if recPars r == 0
                                   then redReturn $ unArg u0
                                   else redReturn $ (Def transpR []) `apply`
                                               (map (fmap lam_i) as ++ [ignoreBlocking sphi,u0])
                         | nelims > 0, Just as <- allApplyElims es, DoHComp <- cmd, Just hCompR <- nameOfHComp kit
                                -> redReturn $ (Def hCompR []) `apply`
                                               (as ++ [ignoreBlocking sphi,fromMaybe __IMPOSSIBLE__ u,u0])

                         | Just as <- allApplyElims es, [] <- recFields r -> compData (recPars r) cmd l (as <$ t) sbA sphi u u0
                     Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons}
                       | and [null pcons | DoHComp  <- [cmd]], Just as <- allApplyElims es -> compData (pars+ixs) cmd l (as <$ t) sbA sphi u u0
                     _          -> fallback

                 _ -> fallback
  where
    compSort DoTransp fallback phi Nothing u0 (IsFam l) = do
      -- TODO should check l is constant
      redReturn $ unArg u0
    compSort DoHComp fallback phi (Just u) u0 (IsNot l) = do
      let getTermLocal = getTerm (builtinHComp ++ " for Set")
      checkPrims <- all isJust <$> sequence [getTerm' builtinPathToEquiv, getTerm' builtinGlue]
      if not checkPrims then fallback else (redReturn =<<) . runNamesT [] $ do
        p2equiv <- getTermLocal builtinPathToEquiv
        tGlue   <- getTermLocal builtinGlue
        tINeg   <- getTermLocal builtinINeg
        io      <- getTermLocal builtinIOne
        l <- open $ Level l
        [phi,e,u0] <- mapM (open . unArg) [phi,u,u0]
        let
          ineg r = pure tINeg <@> r
        pure tGlue <#> l <#> l
               <@> u0 <#> phi <@> (e <@> pure io)
               <@> ilam "o" (\ o -> pure p2equiv <#> (lam "i" $ \ i -> l) <@> (ilam "i" $ \ i -> e <@> ineg i <@> o))
    compSort _ fallback phi u u0 _ = __IMPOSSIBLE__
    compGlue DoHComp psi (Just u) u0 (IsNot (la, lb, bA, phi, bT, e)) = do
      let getTermLocal = getTerm $ (builtinHComp ++ " for " ++ builtinGlue)
      tPOr <- getTermLocal "primPOr"
      tIMax <- getTermLocal builtinIMax
      tIMin <- getTermLocal builtinIMin
      tINeg <- getTermLocal builtinINeg
      tHComp <- getTermLocal builtinHComp
      tEFun  <- getTermLocal builtinEquivFun
      tglue   <- getTermLocal builtin_glue
      tunglue <- getTermLocal builtin_unglue
      io      <- getTermLocal builtinIOne
      (redReturn =<<) . runNamesT [] $ do
        [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]
        [la, lb, bA, phi, bT, e] <- mapM (open . unArg) [la, lb, bA, phi, bT, e]
        let
          hfill la bA phi u u0 i = pure tHComp <#> la
                                               <#> bA
                                               <#> (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               <@> (lam "j" $ \ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <@> (ilam "o" $ \ a -> bA)
                                                     <@> (ilam "o" $ \ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> (ilam "o" $ \ _ -> u0)
                                                   )
                                               <@> u0
          tf i o = hfill lb (bT <..> o) psi u u0 i
          unglue g = pure tunglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> g
          a1 = pure tHComp <#> la <#> bA <#> (pure tIMax <@> psi <@> phi)
                           <@> (lam "i" $ \ i -> pure tPOr <#> la <@> psi <@> phi <@> (ilam "_" $ \ _ -> bA)
                                 <@> (ilam "o" $ \ o -> unglue (u <@> i <..> o))
                                 <@> (ilam "o" $ \ o -> pure tEFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o) <@> tf i o)
                               )
                           <@> (unglue u0)
          t1 = tf (pure io)
        pure tglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> (ilam "o" $ \ o -> t1 o) <@> a1
    compGlue DoTransp psi Nothing u0 (IsFam (la, lb, bA, phi, bT, e)) = do
      let getTermLocal = getTerm $ (builtinTrans ++ " for " ++ builtinGlue)
      tPOr <- getTermLocal "primPOr"
      tIMax <- getTermLocal builtinIMax
      tIMin <- getTermLocal builtinIMin
      tINeg <- getTermLocal builtinINeg
      tHComp <- getTermLocal builtinHComp
      tTrans <- getTermLocal builtinTrans
      tForall  <- getTermLocal builtinFaceForall
      tEFun  <- getTermLocal builtinEquivFun
      tEProof <- getTermLocal builtinEquivProof
      tglue   <- getTermLocal builtin_glue
      tunglue <- getTermLocal builtin_unglue
      io      <- getTermLocal builtinIOne
      iz      <- getTermLocal builtinIZero
      tLMax   <- getTermLocal builtinLevelMax
      tPath   <- getTermLocal builtinPath
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      (redReturn =<<) . runNamesT [] $ do
        comp <- do
          let
            ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
          let forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                              <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                              <@> r
                                              <@> u
          return $ \ la bA phi u u0 ->
            pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                        <@> (lam "i" $ \ i -> ilam "o" $ \ o ->
                                forward la bA i (u <@> i <..> o))
                        <@> forward la bA (pure iz) u0
        let
          transpFill la bA phi u0 i =
            pure tTrans <#> (ilam "j" $ \ j -> la <@> (pure tIMin <@> i <@> j))
                        <@> (ilam "j" $ \ j -> bA <@> (pure tIMin <@> i <@> j))
                        <@> (pure tIMax <@> phi <@> (pure tINeg <@> i))
                        <@> u0
        [psi,u0] <- mapM (open . unArg) [psi,u0]
        glue1 <- do
          g <- open $ (tglue `apply`) . map (setHiding Hidden) . map (subst 0 io) $ [la, lb, bA, phi, bT, e]
          return $ \ t a -> g <@> t <@> a
        unglue0 <- do
          ug <- open $ (tunglue `apply`) . map (setHiding Hidden) . map (subst 0 iz) $ [la, lb, bA, phi, bT, e]
          return $ \ a -> ug <@> a
        [la, lb, bA, phi, bT, e] <- mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [la, lb, bA, phi, bT, e]
        let
          tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <..> o) psi u0 i
          t1 o = tf (pure io) o
          a0 = unglue0 u0
          a1 = comp la bA
                 (pure tIMax <@> psi <@> (pure tForall <@> phi))
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i) <@> psi <@> (pure tForall <@> phi) <@> (ilam "o" $ \ a -> bA <@> i)
                                                     <@> (ilam "o" $ \ _ -> a0)
                                                     <@> (ilam "o" $ \ o -> pure tEFun <#> (lb <@> i)
                                                                                       <#> (la <@> i)
                                                                                       <#> (bT <@> i <..> o)
                                                                                       <#> (bA <@> i)
                                                                                       <@> (e <@> i <..> o)
                                                                                       <@> (tf i o))
                 )
                 a0
          max l l' = pure tLMax <@> l <@> l'
          sigCon x y = pure (Con (sigmaCon kit) ConOSystem []) <@> x <@> y
          w i o = pure tEFun <#> (lb <@> i)
                                                                                       <#> (la <@> i)
                                                                                       <#> (bT <@> i <..> o)
                                                                                       <#> (bA <@> i)
                                                                                       <@> (e <@> i <..> o)
          fiber la lb bA bB f b = (pure (Def (sigmaName kit) []) <#> la <#> lb
                                                            <@> bA
                                                            <@> (lam "a" $ \ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b))
          pe o = -- o : [ φ 1 ]
            pure tPOr <#> max (la <@> pure io) (lb <@> pure io) <@> psi
                      <@> (pure tForall <@> phi)
                      <@> (ilam "o" $ \ _ ->
                             fiber (lb <@> pure io) (la <@> pure io)
                                   (bT <@> (pure io) <..> o) (bA <@> pure io)
                                   (w (pure io) o) a1)
                      <@> (ilam "o" $ \ o -> sigCon u0 (lam "_" $ \ _ -> a1))
                      <@> (ilam "o" $ \ o -> sigCon (t1 o) (lam "_" $ \ _ -> a1))
          t1'alpha o = -- o : [ φ 1 ]
             pure tEProof <#> (lb <@> pure io)
                          <#> (la <@> pure io)
                          <@> (bT <@> pure io <..> o)
                          <@> (bA <@> pure io)
                          <@> (e <@> pure io <..> o)
                          <@> a1
                          <@> (pure tForall <@> phi)
                          <@> pe o
          -- optimize
          t1' o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
          alpha o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaSnd kit)])
          a1' = pure tHComp
                  <#> (la <@> pure io)
                  <#> (bA <@> pure io)
                  <#> (pure tIMax <@> (phi <@> pure io) <@> psi)
                  <@> (lam "j" $ \ j ->
                         pure tPOr <#> (la <@> pure io) <@> (phi <@> pure io) <@> psi <@> (ilam "o" $ \ _ -> bA <@> pure io)
                                   <@> (ilam "o" $ \ o -> alpha o <@@> (w (pure io) o <@> t1' o,a1,j))
                                   <@> (ilam "o" $ \ _ -> a1)
                      )
                  <@> a1
        glue1 (ilam "o" t1') a1'
    compGlue cmd phi u u0 _ = __IMPOSSIBLE__
    compPi :: TranspOrHComp -> ArgName -> FamilyOrNot (Dom Type, Abs Type) -- Γ , i : I
            -> Arg Term -- Γ
            -> Maybe (Arg Term) -- Γ
            -> Arg Term -- Γ
            -> ReduceM Term
    compPi cmd t ab phi u u0 = do
     let getTermLocal = getTerm $ cmdToName cmd ++ " for function types"

     tTrans <- getTermLocal builtinTrans
     tHComp <- getTermLocal builtinHComp
     tINeg <- getTermLocal builtinINeg
     tIMax <- getTermLocal builtinIMax
     iz    <- getTermLocal builtinIZero
     let
      toLevel t = do
        s <- reduce $ getSort t
        case s of
          (Type l) -> return l
          _        -> __IMPOSSIBLE__
      -- mkLam DoTransp = Lam defaultArgInfo
      -- mkLam DoHComp = id
     runNamesT [] $ do
      [la,bA] <- do
        let (x,f) = case ab of
              IsFam (a,_) -> (a, \ a -> runNames [] $ (lam "i" $ const (pure a)))
              IsNot (a,_) -> (a, id)
        lx <- toLevel x
        mapM (open . f) [Level lx, unEl . unDom $ x]
      [phi, u0] <- mapM (open . unArg) [phi, u0]
      u <- traverse open (unArg <$> u)

      glam (getArgInfo (fst $ famThing ab)) (absName $ snd $ famThing ab) $ \ u1 -> do
        case (cmd, ab, u) of
          (DoHComp, IsNot (a , b), Just u) -> do
            bT <- (raise 1 b `absApp`) <$> u1
            let v = u1
            pure tHComp <#> (Level <$> toLevel bT)
                        <#> (pure $ unEl                      $ bT)
                        <#> phi
                        <@> (lam "i" $ \ i -> ilam "o" $ \ o -> gApply (getHiding a) (u <@> i <..> o) v)
                        <@> (gApply (getHiding a) u0 v)
          (DoTransp, IsFam (a , b), Nothing) -> do
            let v i = do
                       let
                         iOrNot j = pure tIMax <@> i <@> (pure tINeg <@> j)
                       pure tTrans <#> (lam "j" $ \ j -> la <@> iOrNot j)
                                 <@> (lam "j" $ \ j -> bA <@> iOrNot j)
                                 <@> (pure tIMax <@> phi <@> i)
                                 <@> u1
                -- Γ , u1 : A[i1] , i : I
                bB v = (consS v $ liftS 1 $ raiseS 1) `applySubst` (absBody b {- Γ , i : I , x : A[i] -})
                tLam = Lam defaultArgInfo
            bT <- bind "i" $ \ i -> bB <$> v i
            -- Γ , u1 : A[i1]
            (pure tTrans <#> (tLam <$> traverse (fmap Level . toLevel) bT)
                         <@> (pure . tLam $ unEl                      <$> bT)
                         <@> phi
                         <@> gApply (getHiding a) u0 (v (pure iz)))
          (_,_,_) -> __IMPOSSIBLE__
    compPathP cmd@DoHComp sphi (Just u) u0 (IsNot l) (IsNot (bA,x,y)) = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for path types"
      tHComp <- getTermLocal builtinHComp
      tINeg <- getTermLocal builtinINeg
      tIMax <- getTermLocal builtinIMax
      tOr   <- getTermLocal "primPOr"
      let
        ineg j = pure tINeg <@> j
        imax i j = pure tIMax <@> i <@> j

      redReturn . runNames [] $ do
         [l,u,u0] <- mapM (open . unArg) [l,u,u0]
         phi      <- open . unArg . ignoreBlocking $ sphi
         [bA, x, y] <- mapM (open . unArg) [bA, x, y]
         lam "j" $ \ j ->
           pure tHComp <#> l
                       <#> (bA <@> j)
                       <#> (phi `imax` (ineg j `imax` j))
                       <@> (lam "i'" $ \ i ->
                            let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> (lam "_" $ \ _ -> bA <@> i)
                            in or phi (ineg j `imax` j)
                                          <@> (ilam "o" $ \ o -> u <@> i <..> o <@@> (x, y, j)) -- a0 <@@> (x <@> i, y <@> i, j)
                                          <@> (or (ineg j) j <@> (ilam "_" $ const x)
                                                                  <@> (ilam "_" $ const y)))
                       <@> (u0 <@@> (x, y, j))
    compPathP cmd@DoTransp sphi Nothing u0 (IsFam l) (IsFam (bA,x,y)) = do
      -- Γ    ⊢ l
      -- Γ, i ⊢ bA, x, y
      let getTermLocal = getTerm $ cmdToName cmd ++ " for path types"
      tINeg <- getTermLocal builtinINeg
      tIMax <- getTermLocal builtinIMax
      tOr   <- getTermLocal "primPOr"
      iz <- getTermLocal builtinIZero
      io <- getTermLocal builtinIOne
      let
        ineg j = pure tINeg <@> j
        imax i j = pure tIMax <@> i <@> j
      comp <- do
        tHComp <- getTermLocal builtinHComp
        tTrans <- getTermLocal builtinTrans
        let forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                            <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                            <@> r
                                            <@> u
        return $ \ la bA phi u u0 ->
          pure tHComp <#> (la <@> pure io)
                      <#> (bA <@> pure io)
                      <#> phi
                      <@> (lam "i" $ \ i -> ilam "o" $ \ o ->
                              forward la bA i (u <@> i <..> o))
                      <@> forward la bA (pure iz) u0
      redReturn . runNames [] $ do
        [l,u0] <- mapM (open . unArg) [l,u0]
        phi      <- open . unArg . ignoreBlocking $ sphi
        [bA, x, y] <- mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [bA, x, y]
        lam "j" $ \ j ->
          comp l (lam "i" $ \ i -> bA <@> i <@> j) (phi `imax` (ineg j `imax` j))
                      (lam "i'" $ \ i ->
                            let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> (lam "_" $ \ _ -> bA <@> i <@> j) in
                                       or phi (ineg j `imax` j)
                                          <@> (ilam "o" $ \ o -> u0 <@@> (x <@> pure iz, y <@> pure iz, j))
                                          <@> (or (ineg j) j <@> (ilam "_" $ const (x <@> i))
                                                                  <@> (ilam "_" $ const (y <@> i))))
                      (u0 <@@> (x <@> pure iz, y <@> pure iz, j))
    compPathP _ sphi u a0 _ _ = __IMPOSSIBLE__
    compId cmd sphi u a0 l bA_x_y = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for " ++ builtinId
      unview <- intervalUnview'
      mConId <- getBuiltinName' builtinConId
      let isConId (Def q _) = Just q == mConId
          isConId _         = False
      sa0 <- reduceB' a0
      -- wasteful to compute b even when cheaper checks might fail
      b <- case u of
             Nothing -> return True
             Just u  -> allComponents unview (unArg . ignoreBlocking $ sphi) (unArg u) isConId
      case mConId of
        Just conid | isConId (unArg . ignoreBlocking $ sa0) , b -> (Just <$>) . (redReturn =<<) $ do
          tHComp <- getTermLocal builtinHComp
          tTrans <- getTermLocal builtinTrans
          tIMin <- getTermLocal "primDepIMin"
          tFace <- getTermLocal "primIdFace"
          tPath <- getTermLocal "primIdPath"
          tPathType <- getTermLocal builtinPath
          runNamesT [] $ do
            let irrInfo = setRelevance Irrelevant defaultArgInfo
            let io = pure $ unview IOne
                iz = pure $ unview IZero
                conId = pure $ Def conid []
            l <- case l of
                   IsFam l -> open . unArg $ l
                   IsNot l -> do
                     open (Lam defaultArgInfo $ NoAbs "_" $ unArg l)
            [p0] <- mapM (open . unArg) [a0]
            p <- case u of
                   Just u -> do
                     u <- open . unArg $ u
                     return $ \ i o -> u <@> i <..> o
                   Nothing -> do
                     return $ \ i o -> p0
            phi      <- open . unArg . ignoreBlocking $ sphi
            [bA, x, y] <-
              case bA_x_y of
                IsFam (bA,x,y) -> mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [bA, x, y]
                IsNot (bA,x,y) -> forM [bA,x,y] $ \ a -> open (Lam defaultArgInfo $ NoAbs "_" $ unArg a)
            let
              eval DoTransp l bA phi _ u0 = pure tTrans <#> l <@> bA <@> phi <@> u0
              eval DoHComp l bA phi u u0 = pure tHComp <#> (l <@> io) <#> (bA <@> io) <#> phi
                                                       <@> u <@> u0
            conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
                  <@> (pure tIMin <@> phi
                                  <@> (ilam "o" $ \ o -> pure tFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
                                                                   <@> (p io o)))
                  <@> (eval cmd l
                                (lam "i" $ \ i -> pure tPathType <#> (l <@> i) <#> (bA <@> i) <@> (x <@> i) <@> (y <@> i))
                                phi
                                (lam "i" $ \ i -> ilam "o" $ \ o -> pure tPath <#> (l <@> i) <#> (bA <@> i)
                                                                                    <#> (x <@> i) <#> (y <@> i)
                                                                                    <@> (p i o)
                                      )
                                (pure tPath <#> (l <@> iz) <#> (bA <@> iz) <#> (x <@> iz) <#> (y <@> iz)
                                                  <@> p0)
                      )
        _ -> return $ Nothing
    allComponents unview phi u p = do
            let
              boolToI b = if b then unview IOne else unview IZero
            as <- decomposeInterval phi
            (and <$>) . forM as $ \ (bs,ts) -> do -- OPTIMIZE: stop at the first False
                 let u' = listS (Map.toAscList $ Map.map boolToI bs) `applySubst` u
                 t <- reduce2Lam u'
                 return $! p t
      where
        reduce2Lam t = do
          t <- reduce' t
          case lam2Abs t of
            t -> Reduce.underAbstraction_ t $ \ t -> do
               t <- reduce' t
               case lam2Abs t of
                 t -> Reduce.underAbstraction_ t reduce'
         where
           lam2Abs (Lam _ t) = t
           lam2Abs t         = Abs "y" (raise 1 t `apply` [argN $ var 0])

    compData _ cmd@DoHComp (IsNot l) (IsNot ps) fsc sphi (Just u) a0 = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"

      let sc = famThing <$> fsc
      tEmpty <- getTermLocal builtinIsOneEmpty
      constrForm <- do
        mz <- getTerm' builtinZero
        ms <- getTerm' builtinSuc
        return $ \ t -> fromMaybe t (constructorForm' mz ms t)
      su  <- reduceB' u
      sa0 <- reduceB' a0
      view   <- intervalView'
      unview <- intervalUnview'
      let f = unArg . ignoreBlocking
          phi = f sphi
          u = f su
          a0 = f sa0
          noRed = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
            where
              su' = case view phi of
                     IZero -> notBlocked $ argN $ runNames [] $ do
                                 [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                                 lam "i" $ \ i -> pure tEmpty <#> l
                                                              <#> (ilam "o" $ \ _ -> c)
                     _     -> su
          sameConHead h u = allComponents unview phi u $ \ t ->
            case constrForm t of
              Con h' _ _ -> h == h'
              _        -> False

      case constrForm a0 of
        Con h _ args -> do
          ifM (not <$> sameConHead h u) noRed $ do
            Constructor{ conComp = (cm,_) } <- theDef <$> getConstInfo (conName h)
            case nameOfHComp cm of
              Just hcompD -> redReturn $ Def hcompD [] `apply` -- TODO pick the right one
                                          (ps ++ map argN [phi,u,a0])
              Nothing        -> noRed
        _ -> noRed
    compData 0 DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = redReturn $ unArg a0
    compData _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"

      let sc = famThing <$> fsc
      tEmpty <- getTermLocal builtinIsOneEmpty
      constrForm <- do
        mz <- getTerm' builtinZero
        ms <- getTerm' builtinSuc
        return $ \ t -> fromMaybe t (constructorForm' mz ms t)
      sa0 <- reduceB' a0
      view   <- intervalView'
      unview <- intervalUnview'
      let f = unArg . ignoreBlocking
          phi = f sphi
          a0 = f sa0
          noRed = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced sa0]
      let lam_i = Lam defaultArgInfo . Abs "i"
      case constrForm a0 of
        Con h _ args -> do
          Constructor{ conComp = (cm,_) } <- theDef <$> getConstInfo (conName h)
          case nameOfTransp cm of
              Just transpD -> redReturn $ Def transpD [] `apply` -- TODO pick the right one
                                          (map (fmap lam_i) ps ++ map argN [phi,a0])
              Nothing        -> noRed
        _ -> noRed
    compData _ _ _ _ _ _ _ _ = __IMPOSSIBLE__
    compPO = __IMPOSSIBLE__

primComp :: TCM PrimitiveImpl
primComp = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (elInf (cl primInterval) --> (el $ cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" (elInf (cl primInterval)) $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          nPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          (nPi' "i" (elInf $ cl primInterval) $ \ i -> pPi' "o" phi $ \ _ -> el' (a <@> i) (bA <@> i)) -->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  one <- primItIsOne
  io  <- primIOne
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    case ts of
      [l,c,phi,u,a0] -> do
        sphi <- reduceB' phi
        vphi <- intervalView $ unArg $ ignoreBlocking sphi
        case vphi of
          IOne -> redReturn (unArg u `apply` [argN io, argN one])
          _    -> do
            let getTermLocal = getTerm $ builtinComp
            tIMax <- getTermLocal builtinIMax
            tINeg <- getTermLocal builtinINeg
            tHComp <- getTermLocal builtinHComp
            tTrans <- getTermLocal builtinTrans
            iz      <- getTermLocal builtinIZero
            (redReturn =<<) . runNamesT [] $ do
              comp <- do
                let
                  ineg j = pure tINeg <@> j
                  imax i j = pure tIMax <@> i <@> j
                let forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                                    <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                                    <@> r
                                                    <@> u
                return $ \ la bA phi u u0 ->
                  pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                              <@> (lam "i" $ \ i -> ilam "o" $ \ o ->
                                      forward la bA i (u <@> i <..> o))
                              <@> forward la bA (pure iz) u0

              [l,c,phi,u,a0] <- mapM (open . unArg) [l,c,phi,u,a0]
              comp l c phi u a0

      _ -> __IMPOSSIBLE__

-- lookupS (listS [(x0,t0)..(xn,tn)]) xi = ti, assuming x0 < .. < xn.
listS :: [(Int,Term)] -> Substitution
listS ((i,t):ts) = singletonS i t `composeS` listS ts
listS []         = IdS


primGlue' :: TCM PrimitiveImpl
primGlue' = do
  requireCubical
  -- Glue' : ∀ {l} (A : Set l) → ∀ φ → (T : Partial (Set a) φ) (f : (PartialP φ \ o → (T o) -> A))
  --            ([f] : PartialP φ \ o → isEquiv (T o) A (f o)) → Set l
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       nPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       nPi' "T" (pPi' "o" φ $ \ o -> el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a)
       --> (sort . tmSort <$> lb))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ts ->
    case ts of
     [la,lb,a,phi,t,e] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la,lb,a] ++ [reduced sphi] ++ map notReduced [t,e])
     _ -> __IMPOSSIBLE__

prim_glue' :: TCM PrimitiveImpl
prim_glue' = do
  requireCubical
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       (pPi' "o" φ $ \ o -> el' lb (t <@> o)) --> (el' la a --> el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ts ->
    case ts of
      [la,lb,bA,phi,bT,e,t,a] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e,t,a])
      _ -> __IMPOSSIBLE__

prim_unglue' :: TCM PrimitiveImpl
prim_unglue' = do
  requireCubical
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       (el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)) --> el' la a)
  view <- intervalView'
  one <- primItIsOne
  mglue <- getPrimitiveName' builtin_glue
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 7 $ \ts ->
    case ts of
      [la,lb,bA,phi,bT,e,b] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> do
           let argOne = setRelevance Irrelevant $ argN one
           tEFun <- getTerm builtin_unglue builtinEquivFun
           redReturn $ tEFun `apply` [lb,la,argH $ unArg bT `apply` [argOne],bA, argN $ unArg e `apply` [argOne],b]
         _    -> do
            sb <- reduceB' b
            case unArg $ ignoreBlocking $ sb of
               Def q [Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply a]
                     | Just q == mglue -> redReturn $ unArg a
               _ -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e] ++ [reduced sb])
      _ -> __IMPOSSIBLE__


-- TODO Andrea: keep reductions that happen under foralls?
primFaceForall' :: TCM PrimitiveImpl
primFaceForall' = do
  requireCubical
  t <- (elInf primInterval --> elInf primInterval) --> elInf primInterval
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ts ->
    case ts of
      [phi] -> do
        sphi <- reduceB' phi
        case unArg $ ignoreBlocking $ sphi of
          Lam _ t -> do
            t <- reduce' t
            case t of
              NoAbs _ t -> redReturn t
              Abs   _ t -> maybe (return $ NoReduction [reduced sphi]) redReturn =<< toFaceMapsPrim t
          _ -> return (NoReduction [reduced sphi])
      _     -> __IMPOSSIBLE__
 where
  toFaceMapsPrim t = do
     view   <- intervalView'
     unview <- intervalUnview'
     us'    <- decomposeInterval t
     fr     <- getTerm builtinFaceForall builtinFaceForall
     let
         v = view t
         us = [ map Left (Map.toList bsm) ++ map Right ts
              | (bsm,ts) <- us'
              , 0 `Map.notMember` bsm
              ]
         fm (i,b) = if b then var (i-1) else unview (INeg (argN (var $ i-1)))
         ffr t = fr `apply` [argN $ Lam defaultArgInfo $ Abs "i" t]
         r = Just $ foldr (\ x r -> unview (IMax (argN x) (argN r))) (unview IZero)
                                 (map (foldr (\ x r -> unview (IMin (argN (either fm ffr x)) (argN r))) (unview IOne)) us)
  --   traceSLn "cube.forall" 20 (unlines [show v, show us', show us, show r]) $
     return $
       case us' of
         [(m,[_])] | Map.null m -> Nothing
         v                      -> r

decomposeInterval :: HasBuiltins m => Term -> m [(Map Int Bool,[Term])]
decomposeInterval t = do
  xs <- decomposeInterval' t
  let isConsistent xs = all (\ xs -> Set.size xs == 1) . Map.elems $ xs  -- optimize by not doing generate + filter
  return [ (Map.map (head . Set.toList) bsm,ts)
            | (bsm,ts) <- xs
            , isConsistent bsm
            ]

decomposeInterval' :: HasBuiltins m => Term -> m [(Map Int (Set Bool),[Term])]
decomposeInterval' t = do
     view   <- intervalView'
     unview <- intervalUnview'
     let f :: IntervalView -> [[Either (Int,Bool) Term]]
         -- TODO handle primIMinDep
         -- TODO? handle forall
         f IZero = mzero
         f IOne  = return []
         f (IMin x y) = do xs <- (f . view . unArg) x; ys <- (f . view . unArg) y; return (xs ++ ys)
         f (IMax x y) = msum $ map (f . view . unArg) [x,y]
         f (INeg x)   = map (either (\ (x,y) -> Left (x,not y)) (Right . unview . INeg . argN)) <$> (f . view . unArg) x
         f (OTerm (Var i [])) = return [Left (i,True)]
         f (OTerm t)          = return [Right t]
         v = view t
     return [ (bsm,ts)
            | xs <- f v
            , let (bs,ts) = partitionEithers xs
            , let bsm     = (Map.fromListWith Set.union . map (id -*- Set.singleton)) bs
            ]

-- | @primEraseEquality : {a : Level} {A : Set a} {x y : A} -> x ≡ y -> x ≡ y@
primEraseEquality :: TCM PrimitiveImpl
primEraseEquality = do
  -- primEraseEquality is incompatible with --without-K
  -- We raise an error warning if --safe is set and a mere warning otherwise
  whenM (optWithoutK <$> pragmaOptions) $
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

  -- BUILTIN REFL maybe a constructor with one (the principal) argument or only parameters.
  -- Get the ArgInfo of the principal argument of refl.
  con@(Con rf ci []) <- primRefl
  minfo <- fmap (setOrigin Inserted) <$> getReflArgInfo rf
  let (refl :: Arg Term -> Term) = case minfo of
        Just ai -> Con rf ci . (:[]) . Apply . setArgInfo ai
        Nothing -> const con

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
  return $ fmap getArgInfo $ headMaybe $ drop (conPars $ theDef def) $ telToList reflTel


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
                Dummy s    -> __IMPOSSIBLE_VERBOSE__ s
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
          redBind (toA v) (\v' -> [v']) $ \x -> do
            b <- f x
            case allMetas b of
              (m:_) -> return $ NoReduction [reduced (Blocked m v)]
              []       -> redReturn =<< fromB b
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
          redBind (toA v)
              (\v' -> [v']) $ \x ->
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

-- Type combinators

infixr 4 -->
infixr 4 .-->
infixr 4 ..-->

(-->), (.-->), (..-->) :: Monad tcm => tcm Type -> tcm Type -> tcm Type
a --> b = garr id a b
a .--> b = garr (const $ Irrelevant) a b
a ..--> b = garr (const $ NonStrict) a b

garr :: Monad tcm => (Relevance -> Relevance) -> tcm Type -> tcm Type -> tcm Type
garr f a b = do
  a' <- a
  b' <- b
  return $ El (funSort (getSort a') (getSort b')) $
    Pi (mapRelevance f $ defaultDom a') (NoAbs "_" b')

gpi :: (MonadTCM tcm, MonadDebug tcm)
    => ArgInfo -> String -> tcm Type -> tcm Type -> tcm Type
gpi info name a b = do
  a <- a
  let dom = defaultNamedArgDom info name a
  b <- addContext (name, dom) b
  let y = stringToArgName name
  return $ El (piSort (getSort a) (Abs y (getSort b)))
              (Pi dom (Abs y b))

hPi, nPi :: (MonadTCM tcm, MonadDebug tcm)
         => String -> tcm Type -> tcm Type -> tcm Type
hPi = gpi $ setHiding Hidden defaultArgInfo
nPi = gpi defaultArgInfo

hPi', nPi' :: (MonadTCM tcm, MonadDebug tcm)
           => String -> NamesT tcm Type -> (NamesT tcm Term -> NamesT tcm Type) -> NamesT tcm Type
hPi' s a b = hPi s a (bind' s b)
nPi' s a b = nPi s a (bind' s b)

pPi' :: (MonadTCM tcm, MonadDebug tcm)
     => String -> NamesT tcm Term -> (NamesT tcm Term -> NamesT tcm Type) -> NamesT tcm Type
pPi' n phi b = toFinitePi <$> nPi' n (elInf $ cl (liftTCM primIsOne) <@> phi) b
 where
   toFinitePi :: Type -> Type
   toFinitePi (El s (Pi d b)) = El s $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
   toFinitePi _               = __IMPOSSIBLE__

#if __GLASGOW_HASKELL__ <= 708
el' :: (Functor m, Applicative m, Monad m)
#else
el' :: Monad m
#endif
    => m Term -> m Term -> m Type
el' l a = El <$> (tmSort <$> l) <*> a

elInf :: Functor m => m Term -> m Type
elInf t = (El Inf <$> t)

nolam :: Term -> Term
nolam = Lam defaultArgInfo . NoAbs "_"

varM :: Monad tcm => Int -> tcm Term
varM = return . var

infixl 9 <@>, <#>

gApply :: Monad tcm => Hiding -> tcm Term -> tcm Term -> tcm Term
gApply h a b = gApply' (setHiding h defaultArgInfo) a b

gApply' :: Monad tcm => ArgInfo -> tcm Term -> tcm Term -> tcm Term
gApply' info a b = do
    x <- a
    y <- b
    return $ x `apply` [Arg info y]

(<@>),(<#>),(<..>) :: Monad tcm => tcm Term -> tcm Term -> tcm Term
(<@>) = gApply NotHidden
(<#>) = gApply Hidden
(<..>) = gApply' (setRelevance Irrelevant defaultArgInfo)

(<@@>) :: Monad tcm => tcm Term -> (tcm Term,tcm Term,tcm Term) -> tcm Term
t <@@> (x,y,r) = do
  t <- t
  x <- x
  y <- y
  r <- r
  return $ t `applyE` [IApply x y r]

list :: TCM Term -> TCM Term
list t = primList <@> t

io :: TCM Term -> TCM Term
io t = primIO <@> t

path :: TCM Term -> TCM Term
path t = primPath <@> t

el :: Functor tcm => tcm Term -> tcm Type
el t = El (mkType 0) <$> t

tset :: Monad tcm => tcm Type
tset = return $ sort (mkType 0)

sSizeUniv :: Sort
sSizeUniv = mkType 0
-- Andreas, 2016-04-14 switching off SizeUniv, unfixing issue #1428
-- sSizeUniv = SizeUniv

tSizeUniv :: Monad tcm => tcm Type
tSizeUniv = tset
-- Andreas, 2016-04-14 switching off SizeUniv, unfixing issue #1428
-- tSizeUniv = return $ El sSizeUniv $ Sort sSizeUniv
-- Andreas, 2015-03-16 Since equality checking for types
-- includes equality checking for sorts, we cannot put
-- SizeUniv in Setω.  (SizeUniv : Setω) == (_0 : suc _0)
-- will first instantiate _0 := Setω, which is wrong.
-- tSizeUniv = return $ El Inf $ Sort SizeUniv

-- | Abbreviation: @argN = 'Arg' 'defaultArgInfo'@.
argN :: e -> Arg e
argN = Arg defaultArgInfo

domN :: e -> Dom e
domN = defaultDom

-- | Abbreviation: @argH = 'hide' 'Arg' 'defaultArgInfo'@.
argH :: e -> Arg e
argH = Arg $ setHiding Hidden defaultArgInfo

domH :: e -> Dom e
domH = setHiding Hidden . defaultDom

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
  , "primNatDivSucAux"    |-> mkPrimFun4 ((\k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Nat -> Nat -> Nat -> Nat -> Nat)
  , "primNatModSucAux"    |->
      let aux :: Nat -> Nat -> Nat -> Nat -> Nat
          aux k m n j | n > j     = mod (n - j - 1) (m + 1)
                      | otherwise = k + n
      in mkPrimFun4 aux
  , "primNatEquality"     |-> mkPrimFun2 ((==) :: Rel Nat)
  , "primNatLess"         |-> mkPrimFun2 ((<)  :: Rel Nat)

  -- Machine words
  , "primWord64ToNat"     |-> mkPrimFun1 (fromIntegral :: Word64 -> Nat)
  , "primWord64FromNat"   |-> mkPrimFun1 (fromIntegral :: Nat -> Word64)

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
  , "primRound"           |-> mkPrimFun1 (round           :: Double -> Integer)
  , "primFloor"           |-> mkPrimFun1 (floor           :: Double -> Integer)
  , "primCeiling"         |-> mkPrimFun1 (ceiling         :: Double -> Integer)
  , "primExp"             |-> mkPrimFun1 (exp             :: Fun Double)
  , "primLog"             |-> mkPrimFun1 (log             :: Fun Double)
  , "primSin"             |-> mkPrimFun1 (sin             :: Fun Double)
  , "primCos"             |-> mkPrimFun1 (cos             :: Fun Double)
  , "primTan"             |-> mkPrimFun1 (tan             :: Fun Double)
  , "primASin"            |-> mkPrimFun1 (asin            :: Fun Double)
  , "primACos"            |-> mkPrimFun1 (acos            :: Fun Double)
  , "primATan"            |-> mkPrimFun1 (atan            :: Fun Double)
  , "primATan2"           |-> mkPrimFun2 (atan2           :: Double -> Double -> Double)
  , "primShowFloat"       |-> mkPrimFun1 (Str . show      :: Double -> Str)

  -- Character functions
  , "primCharEquality"    |-> mkPrimFun2 ((==) :: Rel Char)
  , "primIsLower"         |-> mkPrimFun1 isLower
  , "primIsDigit"         |-> mkPrimFun1 isDigit
  , "primIsAlpha"         |-> mkPrimFun1 isAlpha
  , "primIsSpace"         |-> mkPrimFun1 isSpace
  , "primIsAscii"         |-> mkPrimFun1 isAscii
  , "primIsLatin1"        |-> mkPrimFun1 isLatin1
  , "primIsPrint"         |-> mkPrimFun1 isPrint
  , "primIsHexDigit"      |-> mkPrimFun1 isHexDigit
  , "primToUpper"         |-> mkPrimFun1 toUpper
  , "primToLower"         |-> mkPrimFun1 toLower
  , "primCharToNat"       |-> mkPrimFun1 (fromIntegral . fromEnum :: Char -> Nat)
  , "primNatToChar"       |-> mkPrimFun1 (toEnum . fromIntegral . (`mod` 0x110000)  :: Nat -> Char)
  , "primShowChar"        |-> mkPrimFun1 (Str . show . pretty . LitChar noRange)

  -- String functions
  , "primStringToList"    |-> mkPrimFun1 unStr
  , "primStringFromList"  |-> mkPrimFun1 Str
  , "primStringAppend"    |-> mkPrimFun2 (\s1 s2 -> Str $ unStr s1 ++ unStr s2)
  , "primStringEquality"  |-> mkPrimFun2 ((==) :: Rel Str)
  , "primShowString"      |-> mkPrimFun1 (Str . show . pretty . LitString noRange . unStr)

  -- Other stuff
  , "primEraseEquality"   |-> primEraseEquality
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , "primForce"           |-> primForce
  , "primForceLemma"      |-> primForceLemma
  , "primQNameEquality"   |-> mkPrimFun2 ((==) :: Rel QName)
  , "primQNameLess"       |-> mkPrimFun2 ((<) :: Rel QName)
  , "primShowQName"       |-> mkPrimFun1 (Str . show :: QName -> Str)
  , "primQNameFixity"     |-> mkPrimFun1 (nameFixity . qnameName)
  , "primMetaEquality"    |-> mkPrimFun2 ((==) :: Rel MetaId)
  , "primMetaLess"        |-> mkPrimFun2 ((<) :: Rel MetaId)
  , "primShowMeta"        |-> mkPrimFun1 (Str . show . pretty :: MetaId -> Str)
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
  ]
  where
    (|->) = (,)

lookupPrimitiveFunction :: String -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
  fromMaybe (typeError $ NoSuchPrimitiveFunction x)
            (Map.lookup x primitiveFunctions)

lookupPrimitiveFunctionQ :: QName -> TCM (String, PrimitiveImpl)
lookupPrimitiveFunctionQ q = do
  let s = case qnameName q of
            Name _ x _ _ -> prettyShow x
  PrimImpl t pf <- lookupPrimitiveFunction s
  return (s, PrimImpl t $ pf { primFunName = q })

getBuiltinName :: String -> TCM (Maybe QName)
getBuiltinName b = do
  caseMaybeM (getBuiltin' b) (return Nothing) (Just <.> getName)
  where
  getName v = do
    v <- reduce v
    case unSpine $ v of
      Def x _   -> return x
      Con x _ _ -> return $ conName x
      Lam _ b   -> getName $ unAbs b
      _ -> __IMPOSSIBLE__


isBuiltin :: QName -> String -> TCM Bool
isBuiltin q b = (Just q ==) <$> getBuiltinName b
