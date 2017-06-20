{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}

-- ASR (2017-04-10). TODO: Is this option required by the final
-- version of GHC 8.2.1 (it was required by the RC 1)?
#if __GLASGOW_HASKELL__ >= 802
{-# OPTIONS -Wno-simplifiable-class-constraints #-}
#endif

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive where

import Control.Monad
import Control.Applicative
import Control.Monad.Reader (asks)

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

import Numeric.IEEE ( IEEE(identicalIEEE) )

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

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.Size
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible
import Debug.Trace

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
  traverseTerm  _ = id
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
instance ToTerm Lvl     where toTerm = return $ Level . Max . (:[]) . ClosedLevel . unLvl
instance ToTerm Double  where toTerm = return $ Lit . LitFloat noRange
instance ToTerm Char    where toTerm = return $ Lit . LitChar noRange
instance ToTerm Str     where toTerm = return $ Lit . LitString noRange . unStr
instance ToTerm QName   where toTerm = return $ Lit . LitQName noRange
instance ToTerm MetaId  where
  toTerm = do
    file <- fromMaybe __IMPOSSIBLE__ <$> asks TCM.envCurrentPath
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
          Forced{}   -> irr
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
    Con pos _    [] <- ignoreSharing <$> primIntegerPos
    Con negsuc _ [] <- ignoreSharing <$> primIntegerNegSuc
    toNat         <- fromTerm :: TCM (FromTermFunction Nat)
    return $ \ v -> do
      b <- reduceB' v
      let v'  = ignoreBlocking b
          arg = (<$ v')
      case ignoreSharing $ unArg (ignoreBlocking b) of
        Con c ci [u]
          | c == pos    ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c ci [ignoreReduced u']) $ \ n ->
            redReturn $ fromIntegral n
          | c == negsuc ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c ci [ignoreReduced u']) $ \ n ->
            redReturn $ fromIntegral $ -n - 1
        _ -> return $ NoReduction (reduced b)

instance FromTerm Nat where
  fromTerm = fromLiteral $ \l -> case l of
    LitNat _ n -> Just $ fromInteger n
    _          -> Nothing

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
            a =?= b = ignoreSharing a === ignoreSharing b
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
      isCon (Shared p) = isCon (derefPtr p)
      isCon v          = __IMPOSSIBLE__

      mkList nil cons toA fromA t = do
        b <- reduceB' t
        let t = ignoreBlocking b
        let arg = (<$ t)
        case ignoreSharing $ unArg t of
          Con c ci []
            | c == nil  -> return $ YesReduction NoSimplification []
          Con c ci [x,xs]
            | c == cons ->
              redBind (toA x)
                  (\x' -> notReduced $ arg $ Con c ci [ignoreReduced x',xs]) $ \y ->
              redBind
                  (mkList nil cons toA fromA xs)
                  (fmap $ \xs' -> arg $ Con c ci [defaultArg $ fromA y, xs']) $ \ys ->
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
    case f $ ignoreSharing $ unArg (ignoreBlocking b) of
        Just x  -> return $ YesReduction NoSimplification x
        Nothing -> return $ NoReduction (reduced b)

fromLiteral :: (Literal -> Maybe a) -> TCM (FromTermFunction a)
fromLiteral f = fromReducedTerm $ \t -> case t of
    Lit lit -> f lit
    _       -> Nothing


primINeg' :: TCM PrimitiveImpl
primINeg' = do
  t <- elInf primInterval --> elInf primInterval
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ ts -> do
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
  t <- runNamesT [] $
       nPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       (pPi' "o" φ $ \ o -> elInf $ cl primInterval) --> elInf (cl primInterval)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ ts -> do
    case ts of
      [x,y] -> do
        sx <- reduceB' x
        ix <- intervalView (unArg $ ignoreBlocking sx)
        itisone <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinItIsOne
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
  t <- elInf primInterval --> elInf primInterval --> elInf primInterval
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ ts -> do
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

-- primCoe :: TCM PrimitiveImpl
-- primCoe = do
--   t    <- runNamesT [] $
--           hPi' "a" (el $ cl primLevel) $ \ a -> let seta = Sort . tmSort <$> a in
--           hPi' "A" (sort . tmSort <$> a) $ \ bA ->
--           hPi' "B" (sort . tmSort <$> a) $ \ bB ->
--           nPi' "Q" (El <$> (sortSuc <$> a) <*> cl primPath <#> (lvlSuc <$> a) <#> seta <@> bA <@> bB) $ \ bQ ->
--           nPi' "p" (elInf $ cl primInterval) $ \ p ->
--           nPi' "q" (elInf $ cl primInterval) $ \ q ->
--           (el' a $ bQ <@@> (bA,bB,p)) -->
--           (el' a $ bQ <@@> (bA,bB,q))
--   return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 7 $ \ ts -> do
 --    app <- getPrimitiveTerm' "primPathApply"
 --    case (ts,app) of
 --      ([l,a,b,t,p,q,x],Just app) -> do
 --        let
 --          u = apply app $ map (raise 1) [l,l{- Wrong -},setHiding Hidden a,setHiding Hidden b,t] ++ [defaultArg (var 0)]
 --        (p', q') <- normalise' (p, q)
 --        if p' == q' then redReturn (unArg x)
 --          else do
 --            u' <- normalise' u
 --            if occurrence 0 u' == NoOccurrence then return $ YesReduction YesSimplification (unArg x)
 --                                               else return $ NoReduction (map notReduced ts)
 --      _         -> __IMPOSSIBLE__
 -- where
 --   tmLvlSuc t = Max [Plus 1 $ NeutralLevel mempty $ t]
 --   sortSuc = Type . tmLvlSuc
 --   lvlSuc = Level . tmLvlSuc

primPathAbs' :: TCM PrimitiveImpl
primPathAbs' = do
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       nPi' "f" (elInf (cl primInterval) --> el' a bA) $ \ f ->
       el' a $ cl primPath <#> a <#> bA <@> (f <@> cl primIZero)
                                        <@> (f <@> cl primIOne)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
     [a,bA,f] -> redReturn (unArg f)
     _ -> __IMPOSSIBLE__

primPathApply :: TCM PrimitiveImpl
primPathApply = do
  t <- runNamesT [] $
           hPi' "a" (el (cl primLevel)) $ \ a ->
           hPi' "A" (sort . tmSort <$> a) $ \ bA ->
           hPi' "x" (el' a bA) $ \ x ->
           hPi' "y" (el' a bA) $ \ y ->
           (el' a $ cl primPath <#> a <#> bA <@> x <@> y)
            --> elInf (cl primInterval) --> (el' a bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,a,x,y,p] -> do
        redReturn $ runNames [] $ do
          [p,x,y] <- mapM (open . unArg) [p,x,y]
          lam "i" $ \ i -> do
               [p,x,y,i] <- sequence [p,x,y,i]
               pure $ p `applyE` [IApply x y i]
      _ -> __IMPOSSIBLE__

primPathPApply :: TCM PrimitiveImpl
primPathPApply = do
  t <- runNamesT [] $
           hPi' "a" (el (cl primLevel)) $ \ a ->
           hPi' "A" (elInf (cl primInterval) --> (sort . tmSort <$> a)) $ \ bA ->
           hPi' "x" (el' a (bA <@> cl primIZero)) $ \ x ->
           hPi' "y" (el' a (bA <@> cl primIOne)) $ \ y ->
           (el' a $ cl primPathP <#> a <#> bA <@> x <@> y)
            --> (nPi' "i" (elInf (cl primInterval)) $ \ i -> (el' a (bA <@> i)))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,a,x,y,p] -> do
        redReturn $ runNames [] $ do
          [p,x,y] <- mapM (open . unArg) [p,x,y]
          lam "i" $ \ i -> do
               [p,x,y,i] <- sequence [p,x,y,i]
               pure $ p `applyE` [IApply x y i]
      _ -> __IMPOSSIBLE__

-- ∀ {a}{c}{A : Set a}{x : A}(C : ∀ y → Id x y → Set c) → C x (conid i1 (\ i → x)) → ∀ {y} (p : Id x y) → C y p
primIdJ :: TCM PrimitiveImpl
primIdJ = do
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
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 8 $ \ ts -> do
    unview <- intervalUnview'
    let imax x y = do x' <- x; y' <- y; pure $ unview (IMax (argN x') (argN y'))
        imin x y = do x' <- x; y' <- y; pure $ unview (IMin (argN x') (argN y'))
        ineg x = unview . INeg . argN <$> x
    comp   <- getPrimitiveTerm' "primComp"
    papply <- getPrimitiveTerm' "primPathApply"
    case (ts,comp,papply) of
     ([la,lc,a,x,c,d,y,eq], Just comp, Just papply) -> do
       seq    <- reduceB' eq
       case ignoreSharing $ unArg $ ignoreBlocking $ seq of
         (Def q [Apply la,Apply a,Apply x,Apply y,Apply phi,Apply p]) | Just q == conidn -> do
          redReturn $ runNames [] $ do
             [lc,c,d,la,a,x,y,phi,p] <- mapM (open . unArg) [lc,c,d,la,a,x,y,phi,p]
             let w = pure papply <#> la <#> a <#> x <#> y <@> p
             pure comp <#> (lam "i" $ \ _ -> lc)
                       <@> (lam "i" $ \ i ->
                              c <@> (w <@> i)
                                <@> (pure conid <#> la <#> a <#> x <#> (w <@> i)
                                                <@> (phi `imax` ineg i)
                                                <@> (lam "j" $ \ j -> w <@> imin i j)))
                       <@> phi
                       <@> (lam "i" $ \ _ -> nolam <$> d) -- TODO block
                       <@> d
         _ -> return $ NoReduction $ map notReduced [la,lc,a,x,c,d,y] ++ [reduced seq]
     _ -> __IMPOSSIBLE__

primIdElim' :: TCM PrimitiveImpl
primIdElim' = do
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
       (nPi' "y" (el' a bA) $ \ y ->
        nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
        el' c $ bC <@> y <@> p)
  conid <- primConId
  sin <- primSubIn
  path <- primPath
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 8 $ \ ts -> do
    case ts of
      [a,c,bA,x,bC,f,y,p] -> do
        sp <- reduceB' p
        case ignoreSharing $ unArg $ ignoreBlocking sp of
          Def q [Apply _a, Apply _bA, Apply _x, Apply _y, Apply phi , Apply w] -> do
            y' <- return $ sin `apply` [a,bA                            ,phi,argN $ unArg y]
            w' <- return $ sin `apply` [a,argN $ path `apply` [a,bA,x,y],phi,argN $ unArg w]
            redReturn $ unArg f `apply` [phi, defaultArg y', defaultArg w']
          _ -> return $ NoReduction $ map notReduced [a,c,bA,x,bC,f,y] ++ [reduced sp]
      _ -> __IMPOSSIBLE__

primPFrom1 :: TCM PrimitiveImpl
primPFrom1 = do
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (elInf (cl primInterval) --> (sort . tmSort <$> a)) $ \ bA ->
          (el' a $ bA <@> cl primIOne) -->
          (nPi' "i" (elInf $ cl primInterval) $ \ i ->
           nPi' "j" (elInf $ cl primInterval) $ \ j ->
          pPi' "o" i (\ _ -> el' a (bA <@> (i `imax` j)))
          )
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,a,u,i,j] -> do
        si <- reduceB' i
        vi <- intervalView $ unArg $ ignoreBlocking $ si
        let v = nolam $ unArg u
        case vi of
          IOne -> redReturn v
          _    -> do
            sj <- reduceB' j
            vj <- intervalView $ unArg $ ignoreBlocking $ sj
            case vj of
              IOne -> redReturn v
              _    -> return $ NoReduction $ [notReduced l, notReduced a, notReduced u, reduced si, reduced sj]
      _         -> __IMPOSSIBLE__


primPOr :: TCM PrimitiveImpl
primPOr = do
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel)    $ \ a  ->
          nPi' "i" (elInf $ cl primInterval) $ \ i  ->
          nPi' "j" (elInf $ cl primInterval) $ \ j  ->
          hPi' "A" (pPi' "o" (imax i j) $ \o -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          ((pPi' "i1" i $ \ i1 -> el' a $ bA <..> (cl primIsOne1 <@> i <@> j <@> i1))) -->
          ((pPi' "j1" j $ \ j1 -> el' a $ bA <..> (cl primIsOne2 <@> i <@> j <@> j1))) -->
          (pPi' "o" (imax i j) $ \ o -> el' a $ bA <..> o)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 6 $ \ ts -> do
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
  t <- runNamesT [] $
       (hPi' "a" (el $ cl primLevel) $ \ a ->
        nPi' "A" (sort . tmSort <$> a) $ \ bA ->
        elInf (cl primInterval) --> return (sort $ Inf))
  isOne <- primIsOne
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
      [l,a,phi] -> do
          (El s (Pi d b)) <- runNamesT [] $ do
                             [l,a,phi] <- mapM (open . unArg) [l,a,phi]
                             (elInf $ pure isOne <@> phi) --> el' l a
          redReturn $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      _ -> __IMPOSSIBLE__

primPartialP' :: TCM PrimitiveImpl
primPartialP' = do
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
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v

primSubOut' :: TCM PrimitiveImpl
primSubOut' = do
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          hPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          hPi' "u" (elInf $ cl primPartial <#> a <@> bA <@> phi) $ \ u ->
          elInf (cl primSub <#> a <@> bA <@> phi <@> u) --> el' (Sort . tmSort <$> a) bA
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [a,bA,phi,u,x] -> do
        view <- intervalView'
        sphi <- reduceB' phi
        case view $ unArg $ ignoreBlocking sphi of
          IOne -> redReturn =<< (return (unArg u) <..> (fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinItIsOne))
          _ -> do
            sx <- reduceB' x
            mSubIn <- getBuiltinName' builtinSubIn
            case ignoreSharing $ unArg $ ignoreBlocking $ sx of
              Def q [_,_,_, Apply t] | Just q == mSubIn -> redReturn (unArg t)
              _ -> return $ NoReduction $ map notReduced [a,bA] ++ [reduced sphi, notReduced u, reduced sx]
      _ -> __IMPOSSIBLE__

primIdFace' :: TCM PrimitiveImpl
primIdFace' = do
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       (el' a $ cl primId <#> a <#> bA <@> x <@> y)
       --> elInf (cl primInterval)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        case ignoreSharing $ unArg (ignoreBlocking st) of
          Def q [_,_,_,_, Apply phi,_] | Just q == mConId -> redReturn (unArg phi)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__

primIdPath' :: TCM PrimitiveImpl
primIdPath' = do
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       (el' a $ cl primId <#> a <#> bA <@> x <@> y)
       --> (el' a $ cl primPath <#> a <#> bA <@> x <@> y)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        case ignoreSharing $ unArg (ignoreBlocking st) of
          Def q [_,_,_,_,_,Apply w] | Just q == mConId -> redReturn (unArg w)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__

primComp :: TCM PrimitiveImpl
primComp = do
  t    <- runNamesT [] $
          hPi' "a" (elInf (cl primInterval) --> (el $ cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" (elInf (cl primInterval)) $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          nPi' "φ" (elInf $ cl primInterval) $ \ phi ->
          (nPi' "i" (elInf $ cl primInterval) $ \ i -> pPi' "o" phi $ \ _ -> el' (a <@> i) (bA <@> i)) -->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  one <- primItIsOne
  tempty <- primIsOneEmpty
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    unview <- intervalUnview'
    pathV  <- pathView'
    let
        ineg t = (unview . INeg . argN) <$> t
        imax u t = do u <- u; t <- t; return $ unview (IMax (argN u) (argN t))
        iz :: Applicative m => m Term
        iz = pure $ unview IZero
    case ts of
      [l,c,phi,u,a0] -> do
        sphi <- reduceB' phi
        vphi <- intervalView $ unArg $ ignoreBlocking sphi
        io   <- intervalUnview IOne
        tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOneEmpty
        case vphi of
          IOne -> redReturn (unArg u `apply` [argN io, argN one])
          _    -> do
           sc <- reduceB' c
           let fallback = return $ NoReduction [notReduced l,reduced sc, reduced sphi, u', notReduced a0]
                 where
                   u' = case vphi of
                          IZero -> reduced $ notBlocked $ argN $ runNames [] $ do
                                      [l,c] <- mapM (open . unArg) [l, ignoreBlocking sc]
                                      lam "i" $ \ i -> pure tEmpty <#> (l <@> i)
                                                                   <#> (ilam "o" $ \ _ -> c <@> i)
                          _     -> notReduced u

           case ignoreSharing $ unArg $ ignoreBlocking sc of
             Lam _info t -> do
               t <- reduce' t
               mGlue <- getPrimitiveName' builtinGlue
               mId   <- getBuiltinName' builtinId
               mPath <- getBuiltinName' builtinPath
               case ignoreSharing $ absBody t of
                 Pi a b   -> redReturn =<< compPi t a b (ignoreBlocking sphi) u a0

                 s@Sort{} -> compSort fallback iz io ineg phi u a0 s

                 Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply f, Apply pf] | Just q == mGlue -> do
                   compGlue phi u a0 la lb bA phi' bT f pf

                 -- Path/PathP
                 d | PathType _ _ _ bA x y <- pathV (El Prop d) -> do
                   compPathP iz ineg imax sphi u a0 l bA x y

                 Def q [Apply _ , Apply bA , Apply x , Apply y] | Just q == mId -> do
                   maybe fallback return =<< compId sphi u a0 l bA x y

                 Def q es -> do
                   info <- getConstInfo q
                   case theDef info of
                     Record{recComp = Just compR} | Just as <- allApplyElims es
                                -> redReturn $ (Def compR []) `apply`
                                               (map (fmap lam_i) as ++ [ignoreBlocking sphi,u,a0])
                     Record{recComp = Nothing, recFields = []}
                                | Just as <- allApplyElims es -> compData l as sc sphi u a0
                     Datatype{} | Just as <- allApplyElims es -> compData l as sc sphi u a0
                     _          -> fallback

                 _ -> fallback

             _ -> fallback

      _ -> __IMPOSSIBLE__

 where
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
        case lam2Abs $ ignoreSharing t of
          t -> Reduce.underAbstraction_ t $ \ t -> do
             t <- reduce' t
             case lam2Abs $ ignoreSharing t of
               t -> Reduce.underAbstraction_ t reduce'
       where
         lam2Abs (Lam _ t) = t
         lam2Abs t         = Abs "y" (raise 1 t `apply` [argN $ var 0])

  compData l ps sc sphi u a0 = do
    tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOneEmpty
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
                               lam "i" $ \ i -> pure tEmpty <#> (l <@> i)
                                                            <#> (ilam "o" $ \ _ -> c <@> i)
                   _     -> su
        sameConHead h u = allComponents unview phi u $ \ t ->
          case ignoreSharing t of
            Con h' _ _ -> h == h'
            _        -> False

    case ignoreSharing a0 of
      Con h _ args -> do
        ifM (not <$> sameConHead h u) noRed $ do
          Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
          case cm of
            Just (compD,_) -> redReturn $ Def compD [] `apply`
                                        (map (fmap lam_i) ps ++ map argN [phi,u,a0])
            Nothing        -> noRed
      _ -> noRed

  compGlue phi u a0 la lb bA phi' bT f pf = do
    let xs = map (\ x -> runNames [] $ lam "i" (\ _ -> pure (unArg x))) [la,lb,bA,phi',bT,f,pf]
    (redReturn =<<) . runNamesT [] $ do
      tCGlue <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinCompGlue
      [phi,u,a0] <- mapM (open . unArg) [phi,u,a0]
      [la,lb,bA,phi',bT,f,pf] <- mapM open xs
      pure tCGlue <#> la <#> lb <@> bA <@> phi' <@> bT <@> f <@> pf <@> phi <@> u <@> a0

  compSort fallback iz io ineg phi u a0 s = do
   checkPrims <- all isJust <$> sequence [getBuiltin' builtinPathToEquiv, getPrimitiveTerm' builtinGlue]
   if not checkPrims then fallback else (redReturn =<<) . runNamesT [] $ do
    p2equiv <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinPathToEquiv
    tGlue <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' builtinGlue
    tComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primComp"
    tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOneEmpty
    l <- open $ runNames [] (lam "i" (\ _ -> pure $ Level $ lvlView s))
    [phi,e,a0] <- mapM (open . unArg) [phi,u,a0]
    let transp p = pure tComp <#> l <@> p <@> iz
                              <@> lam "i" (\ i -> pure tEmpty <#> (l <@> i)
                                                              <#> (ilam "o" $ \ _ -> p <@> i))
    pure tGlue <#> (l <@> iz) <#> (l <@> pure io)
               <@> a0 <@> phi <@> (e <@> pure io)
               <@> ilam "o" (\ o -> transp (lam "i" $ \ i -> e <@> ineg i <@> o))
               <@> ilam "o" (\ o -> pure p2equiv <#> l <@> (ilam "i" $ \ i -> e <@> ineg i <@> o))

  compId sphi u a0 l bA x y = do
    unview <- intervalUnview'
    mConId <- getBuiltinName' builtinConId
    let isConId (Def q _) = Just q == mConId
        isConId _         = False
    sa0 <- reduceB' a0
    -- wasteful to compute b even when cheaper checks might fail
    b <- allComponents unview (unArg . ignoreBlocking $ sphi) (unArg u) isConId
    case mConId of
      Just conid | isConId (unArg . ignoreBlocking $ sa0) , b -> (Just <$>) . (redReturn =<<) $ do
        tComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primComp"
        tIMin <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primDepIMin"
        tFace <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primIdFace"
        tPath <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primIdPath"
        tPathType <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinPath
        runNamesT [] $ do
          let irrInfo = setRelevance Irrelevant defaultArgInfo
          let io = pure $ unview IOne
              iz = pure $ unview IZero
              conId = pure $ Def conid []
          [l,p,p0] <- mapM (open . unArg) [l,u,a0]
          phi      <- open . unArg . ignoreBlocking $ sphi
          [bA, x, y] <- mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [bA, x, y]
          conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
                <@> (pure tIMin <@> phi
                                <@> (ilam "o" $ \ o -> pure tFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
                                                                 <@> (gApply' irrInfo (p <@> io) o)))
                <@> (pure tComp <#> l
                                <@> (lam "i" $ \ i -> pure tPathType <#> (l <@> i) <#> (bA <@> i) <@> (x <@> i) <@> (y <@> i))
                                <@> phi
                                <@> (lam "i" $ \ i -> ilam "o" $ \ o -> pure tPath <#> (l <@> i) <#> (bA <@> i)
                                                                                  <#> (x <@> i) <#> (y <@> i)
                                                                                  <@> (gApply' irrInfo (p <@> i) o)
                                    )
                                <@> (pure tPath <#> (l <@> iz) <#> (bA <@> iz) <#> (x <@> iz) <#> (y <@> iz)
                                                <@> p0)
                    )
      _ -> return $ Nothing

  compPathP iz ineg imax sphi u a0 l bA x y = do
    tComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primComp"
    tOr   <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primPOr"
    redReturn . runNames [] $ do
       [l,p,p0] <- mapM (open . unArg) [l,u,a0]
       phi      <- open . unArg . ignoreBlocking $ sphi
       [bA, x, y] <- mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [bA, x, y]
       lam "j" $ \ j ->
         pure tComp <#> l <@> (lam "i'" $ \ i -> bA <@> i <@> j) <@> (phi `imax` (ineg j `imax` j))
                    <@> (lam "i'" $ \ i ->
                          let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> (lam "_" $ \ _ -> bA <@> i) in
                                     or phi (ineg j `imax` j)
                                        <@> (ilam "o" $ \ o -> p <@> i <@> o <@@> (x <@> i, y <@> i, j))
                                        <@> (or (ineg j) j <@> (ilam "_" $ const (x <@> i))
                                                                <@> (ilam "_" $ const (y <@> i))))
                    <@> (p0 <@@> (x <@> iz, y <@> iz, j))

  lam_i = Lam defaultArgInfo . Abs "i"


  compPi :: Abs Term -> Dom Type -> Abs Type -> -- Γ , i : I
               Arg Term -- phi -- Γ
            -> Arg Term -- u -- function -- Γ
            -> Arg Term -- λ0 -- fine -- Γ
            -> ReduceM Term
  compPi t a b phi u a0 = do
   unview <- intervalUnview'
   tComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primComp"
   tFrom1 <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primPFrom1"
   let
    ineg t = (unview . INeg . argN) t
    imax u t = unview (IMax (argN u) (argN t))
    toLevel (Type l) = l
    toLevel _        = __IMPOSSIBLE__
    termComp = pure tComp
    v' = termComp         <#> pure (lam_j sa)
                          <@> (pure $ lam_j  -- Γ , u1 : A[i1] , i : I , j : I
                                            at)
                          <@> varM 0 -- Γ , u1 : A[i1] , i : I
                          <@> (lam_j <$> (pure tFrom1 <#> (pure $ lam_i sa') <#> (pure $ lam_i $ unEl $ unDom a')
                                                     <@> pure (raise 2 u1) <@> varM 1 <@> (ineg <$> varM 0)))
                          <@> (pure $ raise 1 u1)
    u1 = var 0  -- Γ , u1 : A[i1]
    a' = applySubst (liftS 1 $ raiseS 3) a -- Γ , u1 : A[i1] , i : I , j : I , i' : I
    sa' = Level . toLevel $ getSort a'
    a'' = (applySubst (singletonS 0 iOrNj) a')
    sa = Level . toLevel $ getSort a''

    at = unEl . unDom $ a''

    iOrNj = var 1 `imax` (ineg $ var 0)  -- Γ , u1 : A[i1] , i : I , j : I
               -- Γ , u1 : A[i1] , i : I
    i0 = unview IZero
    lam = Lam defaultArgInfo
    lam_i m = lam (mkAbs (absName t) m)
    lam_j m = lam (mkAbs "j" m)
    lam_o m = lam (mkAbs "o" m)
   v <- v'
   let
    b'  = absBody $ b -- Γ , i : I , x : A[i]
    b''' = applySubst (consS v $ liftS 1 $ raiseS 1) b' -- Γ , u1 : A[i1] , i : I
    b'' = unEl b'''
    sb = Level . toLevel $ getSort b'''
   (Lam (getArgInfo a) . mkAbs (absName b)) <$>

     -- Γ , u1 : A[i1]
      (termComp <#> pure (lam_i sb) <@> pure (lam_i -- Γ , u1 : A[i1] , i : I
                                      b'')
                      <@> pure (raise 1 (unArg phi))
                      <@> (lam_i . lam_o <$> -- Γ , u1 : A[i1] , i : I, o : IsOne φ
                                  (gApply (getHiding a) (pure (raise 3 (unArg u)) <@> varM 1 <@> varM 0) (pure (raise 1 v)))) -- block until φ = 1?
                      <@> (gApply (getHiding a) (pure $ raise 1 (unArg a0)) (subst 0 i0 <$> pure v))) -- Γ , u1 : A[i1]


-- lookupS (listS [(x0,t0)..(xn,tn)]) xi = ti, assuming x0 < .. < xn.
listS :: [(Int,Term)] -> Substitution
listS ((i,t):ts) = singletonS i t `composeS` listS ts
listS []         = IdS


primGlue' :: TCM PrimitiveImpl
primGlue' = do
  -- Glue' : ∀ {l} (A : Set l) → ∀ φ → (T : Partial (Set a) φ) (f : (PartialP φ \ o → (T o) -> A))
  --            ([f] : PartialP φ \ o → isEquiv (T o) A (f o)) → Set l
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       nPi' "A" (sort . tmSort <$> la) $ \ a ->
       nPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       nPi' "T" (pPi' "o" φ $ \ o -> el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       nPi' "f" (pPi' "o" φ $ \ o -> el' lb (t <@> o) --> el' la a) $ \ f ->
       (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primIsEquiv <#> lb <#> la <@> (t <@> o) <@> a <@> (f <@> o))
       --> (sort . tmSort <$> lb))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 7 $ \ts ->
    case ts of
     [la,lb,a,phi,t,f,pf] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la,lb,a] ++ [reduced sphi] ++ map notReduced [t,f,pf])
     _ -> __IMPOSSIBLE__

prim_glue' :: TCM PrimitiveImpl
prim_glue' = do
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "f" (pPi' "o" φ $ \ o -> el' lb (t <@> o) --> el' la a) $ \ f ->
       hPi' "pf" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primIsEquiv <#> lb <#> la <@> (t <@> o) <@> a <@> (f <@> o)) $ \ pf ->
       (pPi' "o" φ $ \ o -> el' lb (t <@> o)) --> (el' la a --> el' lb (cl primGlue <#> la <#> lb <@> a <@> φ <@> t <@> f <@> pf)))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 9 $ \ts ->
    case ts of
      [la,lb,bA,phi,bT,f,pf,t,a] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,f,pf,t,a])
      _ -> __IMPOSSIBLE__

prim_unglue' :: TCM PrimitiveImpl
prim_unglue' = do
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "f" (pPi' "o" φ $ \ o -> el' lb (t <@> o) --> el' la a) $ \ f ->
       hPi' "pf" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primIsEquiv <#> lb <#> la <@> (t <@> o) <@> a <@> (f <@> o)) $ \ pf ->
       (el' lb (cl primGlue <#> la <#> lb <@> a <@> φ <@> t <@> f <@> pf)) --> el' la a)
  view <- intervalView'
  one <- primItIsOne
  mglue <- getPrimitiveName' builtin_glue
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 8 $ \ts ->
    case ts of
      [la,lb,bA,phi,bT,f,pf,b] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg f `apply` [argN one,b]
         _    -> do
            sb <- reduceB' b
            case ignoreSharing $ unArg $ ignoreBlocking $ sb of
               Def q [Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply a]
                     | Just q == mglue -> redReturn $ unArg a
               _ -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,f,pf] ++ [reduced sb])
      _ -> __IMPOSSIBLE__



-- TODO Andrea: keep reductions that happen under foralls?
primFaceForall' :: TCM PrimitiveImpl
primFaceForall' = do
  t <- (elInf primInterval --> elInf primInterval) --> elInf primInterval
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
    case ts of
      [phi] -> do
        sphi <- reduceB' phi
        case ignoreSharing $ unArg $ ignoreBlocking $ sphi of
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
     fr     <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' builtinFaceForall
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


-- | @trustMe : {a : Level} {A : Set a} {x y : A} -> x ≡ y@
primTrustMe :: TCM PrimitiveImpl
primTrustMe = do
  -- primTrustMe is not --safe
  whenM (Lens.getSafeMode <$> commandLineOptions) $ warning SafeFlagPrimTrustMe

  -- Get the name and type of BUILTIN EQUALITY
  eq   <- primEqualityName
  eqTy <- defType <$> getConstInfo eq
  -- E.g. @eqTy = eqTel → Set a@ where @eqTel = {a : Level} {A : Set a} (x y : A)@.
  TelV eqTel eqCore <- telView eqTy
  let eqSort = case ignoreSharing $ unEl eqCore of
        Sort s -> s
        _      -> __IMPOSSIBLE__

  -- Construct the type of primTrustMe.
  -- E.g., type of @trustMe : {a : Level} {A : Set a} {x y : A} → eq {a} {A} x y@.
  let t = telePi_ (fmap hide eqTel) $ El eqSort $ Def eq $ map Apply $ teleArgs eqTel

  -- BUILTIN REFL maybe a constructor with one (the principal) argument or only parameters.
  -- Get the ArgInfo of the principal argument of refl.
  con@(Con rf ci []) <- ignoreSharing <$> primRefl
  minfo <- fmap (setOrigin Inserted) <$> getReflArgInfo rf
  let (refl :: Arg Term -> Term) = case minfo of
        Just ai -> Con rf ci . (:[]) . setArgInfo ai
        Nothing -> const con

  -- The implementation of primTrustMe:
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ (size eqTel) $ \ ts -> do
    let (u, v) = fromMaybe __IMPOSSIBLE__ $ last2 ts
    -- Andreas, 2013-07-22.
    -- Note that we cannot call the conversion checker here,
    -- because 'reduce' might be called in a context where
    -- some bound variables do not have a type (just 'Prop),
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
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 6 $ \ ts ->
    case ts of
      [a, b, s, t, u, f] -> do
        u <- reduceB' u
        let isWHNF Blocked{} = return False
            isWHNF (NotBlocked _ u) =
              case ignoreSharing $ unArg u of
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
                Shared{}   -> __IMPOSSIBLE__

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
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Level $ Max []

mkPrimLevelSuc :: TCM PrimitiveImpl
mkPrimLevelSuc = do
  t <- primType (id :: Lvl -> Lvl)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ ~[a] -> do
    l <- levelView' $ unArg a
    redReturn $ Level $ levelSuc l

mkPrimLevelMax :: TCM PrimitiveImpl
mkPrimLevelMax = do
  t <- primType (max :: Op Lvl)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ ~[a, b] -> do
    Max as <- levelView' $ unArg a
    Max bs <- levelView' $ unArg b
    redReturn $ Level $ levelMax $ as ++ bs

mkPrimFun1TCM :: (FromTerm a, ToTerm b, TermLike b) =>
                 TCM Type -> (a -> ReduceM b) -> TCM PrimitiveImpl
mkPrimFun1TCM mt f = do
    toA   <- fromTerm
    fromB <- toTermR
    t     <- mt
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
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
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
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
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ts ->
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
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ts ->
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
  return $ El (getSort a' `sLub` getSort b') $
    Pi (mapRelevance f $ defaultDom a') (NoAbs "_" b')

gpi :: MonadTCM tcm => ArgInfo -> String -> tcm Type -> tcm Type -> tcm Type
gpi info name a b = do
  a <- a
  b <- addContext' (name, defaultArgDom info a) b
  let y = stringToArgName name
  return $ El (getSort a `dLub` Abs y (getSort b))
              (Pi (defaultArgDom info a) (Abs y b))

hPi, nPi :: MonadTCM tcm => String -> tcm Type -> tcm Type -> tcm Type
hPi = gpi $ setHiding Hidden defaultArgInfo
nPi = gpi defaultArgInfo

hPi', nPi' :: MonadTCM tcm => String -> NamesT tcm Type -> (NamesT tcm Term -> NamesT tcm Type) -> NamesT tcm Type
hPi' s a b = hPi s a (bind' s b)
nPi' s a b = nPi s a (bind' s b)

pPi' :: MonadTCM tcm => String -> NamesT tcm Term -> (NamesT tcm Term -> NamesT tcm Type) -> NamesT tcm Type
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

tSetOmega :: Monad tcm => tcm Type
tSetOmega = return $ sort Inf

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

  -- Level functions
  , "primLevelZero"       |-> mkPrimLevelZero
  , "primLevelSuc"        |-> mkPrimLevelSuc
  , "primLevelMax"        |-> mkPrimLevelMax

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
  , "primFloatNumericalEquality" |-> mkPrimFun2 ((==)     :: Rel Double)
  , "primFloatNumericalLess"     |-> mkPrimFun2 (floatLt  :: Rel Double)
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
  , "primTrustMe"         |-> primTrustMe
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
  , "primPathApply"       |-> primPathApply
  , "primPathPApply"      |-> primPathPApply
  , "primIMin"            |-> primIMin'
  , "primIMax"            |-> primIMax'
  , "primINeg"            |-> primINeg'
--  , "primCoe"             |-> primCoe
  , "primPOr"             |-> primPOr
  , "primComp"            |-> primComp
  , "primPFrom1"          |-> primPFrom1
  , "primIdJ"             |-> primIdJ
  , "primPartial"         |-> primPartial'
  , "primPartialP"        |-> primPartialP'
  , "primPathAbs"         |-> primPathAbs'
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

floatEq :: Double -> Double -> Bool
floatEq x y = identicalIEEE x y || (isNaN x && isNaN y)

floatLt :: Double -> Double -> Bool
floatLt x y =
  case compareFloat x y of
    LT -> True
    _  -> False
  where
    -- Also implemented in the GHC/UHC backends
    compareFloat :: Double -> Double -> Ordering
    compareFloat x y
      | identicalIEEE x y          = EQ
      | isNegInf x                 = LT
      | isNegInf y                 = GT
      | isNaN x && isNaN y         = EQ
      | isNaN x                    = LT
      | isNaN y                    = GT
      | otherwise                  = compare x y
    isNegInf z = z < 0 && isInfinite z

lookupPrimitiveFunction :: String -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
  fromMaybe (typeError $ NoSuchPrimitiveFunction x)
            (Map.lookup x primitiveFunctions)

lookupPrimitiveFunctionQ :: QName -> TCM (String, PrimitiveImpl)
lookupPrimitiveFunctionQ q = do
  let s = case qnameName q of
            Name _ x _ _ -> show x
  PrimImpl t pf <- lookupPrimitiveFunction s
  return (s, PrimImpl t $ pf { primFunName = q })

getBuiltinName :: String -> TCM (Maybe QName)
getBuiltinName b = do
  caseMaybeM (getBuiltin' b) (return Nothing) (Just <.> getName)
  where
  getName v = do
    v <- reduce v
    case unSpine $ ignoreSharing v of
      Def x _   -> return x
      Con x _ _ -> return $ conName x
      Lam _ b   -> getName $ unAbs b
      _ -> __IMPOSSIBLE__


isBuiltin :: QName -> String -> TCM Bool
isBuiltin q b = (Just q ==) <$> getBuiltinName b
