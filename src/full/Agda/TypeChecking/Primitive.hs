{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UndecidableInstances       #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive where

import Control.Monad
import Control.Applicative
import Control.Monad.Reader (asks)

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable (traverse)
import Data.Monoid (mempty)

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty ()

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import qualified Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Level
import Agda.TypeChecking.Quote (QuotingKit, quoteTermWithKit, quoteTypeWithKit, quoteClauseWithKit, quotingKit)
import Agda.TypeChecking.Pretty ()  -- instances only
import Agda.TypeChecking.MetaVars (allMetas)
import Agda.TypeChecking.Free

import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.Maybe

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
    return $ \ (ArgInfo h r) -> info `applys`
      [ case h of
          NotHidden -> vis
          Hidden    -> hid
          Instance  -> ins
      , case r of
          Relevant   -> rel
          Irrelevant -> irr
          NonStrict  -> rel
          Forced{}   -> irr
          UnusedArg  -> irr
      ]

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
    Con pos    [] <- ignoreSharing <$> primIntegerPos
    Con negsuc [] <- ignoreSharing <$> primIntegerNegSuc
    toNat         <- fromTerm :: TCM (FromTermFunction Nat)
    return $ \ v -> do
      b <- reduceB' v
      let v'  = ignoreBlocking b
          arg = (<$ v')
      case ignoreSharing $ unArg (ignoreBlocking b) of
        Con c [u]
          | c == pos    ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c [ignoreReduced u']) $ \ n ->
            redReturn $ fromIntegral n
          | c == negsuc ->
            redBind (toNat u)
              (\ u' -> notReduced $ arg $ Con c [ignoreReduced u']) $ \ n ->
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
            Con x [] === Con y []   = x == y
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
      isCon (Con c _)  = return c
      isCon (Shared p) = isCon (derefPtr p)
      isCon v          = __IMPOSSIBLE__

      mkList nil cons toA fromA t = do
        b <- reduceB' t
        let t = ignoreBlocking b
        let arg = (<$ t)
        case ignoreSharing $ unArg t of
          Con c []
            | c == nil  -> return $ YesReduction NoSimplification []
          Con c [x,xs]
            | c == cons ->
              redBind (toA x)
                  (\x' -> notReduced $ arg $ Con c [ignoreReduced x',xs]) $ \y ->
              redBind
                  (mkList nil cons toA fromA xs)
                  (fmap $ \xs' -> arg $ Con c [defaultArg $ fromA y, xs']) $ \ys ->
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

primINeg :: TCM PrimitiveImpl
primINeg = do
  t <- el primInterval --> el primInterval
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

primIBin :: IntervalView -> IntervalView -> TCM PrimitiveImpl
primIBin unit absorber = do
  t <- el primInterval --> el primInterval --> el primInterval
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


primIMin :: TCM PrimitiveImpl
primIMin = primIBin IOne IZero

primIMax :: TCM PrimitiveImpl
primIMax = primIBin IZero IOne

primCoe :: TCM PrimitiveImpl
primCoe = do
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          hPi "B" (return $ sort $ varSort 1) $
          nPi "Q" (El (Type $ varLvlSuc 2) <$> primPath <#> (return $ Level $ varLvlSuc 2) <#> (return $ Sort (varSort 2)) <@> varM 1 <@> varM 0) $
          nPi "p" (el primInterval) $
          nPi "q" (el primInterval) $
          (El (varSort 5) <$> getPrimitiveTerm "primPathApply" <#> (return $ Level $ varLvlSuc 5) <#> (return $ Sort (varSort 5))
               <#> varM 4 <#> varM 3 <@> varM 2 <@> varM 1) -->
          (El (varSort 5) <$> getPrimitiveTerm "primPathApply" <#> (return $ Level $ varLvlSuc 5) <#> (return $ Sort (varSort 5))
               <#> varM 4 <#> varM 3 <@> varM 2 <@> varM 0)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 7 $ \ ts -> do
    case ts of
      [l,a,b,t,p,q,x] -> do
        app <- (`Def` []) <$> primFunName <$> fromMaybe __IMPOSSIBLE__ <$> getPrimitive' "primPathApply"
        let
          u = apply app $ map (raise 1) [l,l{- Wrong -},setHiding Hidden a,setHiding Hidden b,t] ++ [defaultArg (var 0)]
        (p', q') <- normalise' (p, q)
        if p' == q' then redReturn (unArg x)
          else do
            u' <- normalise' u
            if occurrence 0 u' == NoOccurrence then return $ YesReduction YesSimplification (unArg x)
                                               else return $ NoReduction (map notReduced ts)
      _         -> __IMPOSSIBLE__
 where
   varLvlSuc n = Max [Plus 1 $ NeutralLevel mempty $ var n]

primPathApply :: TCM PrimitiveImpl
primPathApply = do
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          hPi "x" (El (varSort 1) <$> varM 0) $
          hPi "y" (El (varSort 2) <$> varM 1) $
          (El (varSort 3) <$> primPath <#> varM 3 <#> varM 2 <@> varM 1 <@> varM 0)
          --> el primInterval --> (El (varSort 3) <$> varM 2)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 6 $ \ ts -> do
    pathAbs <- getBuiltinName' builtinPathAbs
    case ts of
      [l,a,x,y,p,r] -> do
        sr <- reduceB' r
        let r = ignoreBlocking sr
        rv <- intervalView $ unArg r
        case rv of
           IZero -> redReturn (unArg x)
           IOne  -> redReturn (unArg y)
           _     -> do
             sp <- reduceB' p
             let p = unArg $ ignoreBlocking sp
             case p of
               Def q [Apply l,Apply a,Apply t]
                   | Just q == pathAbs -> redReturn $ apply (unArg t) [r]
               _                       -> return $ NoReduction $ [notReduced l,notReduced a,notReduced x,notReduced y,reduced sp,reduced sr]

      _ -> __IMPOSSIBLE__

primOutPartial :: TCM PrimitiveImpl
primOutPartial = do
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          (El (varSort 1) <$> primPartial <#> varM 1 <@> varM 0 <@> intervalUnview IOne) -->
          (El (varSort 1) <$> varM 0)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
     [l,a,u] -> redReturn (unArg u)
     _ -> __IMPOSSIBLE__

-- ∀ {a}{c}{A : Set a}{x : A}(C : ∀ y → Id x y → Set c) → C x (conid i1 (\ i → x)) → ∀ {y} (p : Id x y) → C y p
primIdJ :: TCM PrimitiveImpl
primIdJ = do
  let lam_i t = Lam defaultArgInfo (mkAbs "i" t)
  t <- hPi "a" (el primLevel) $
       hPi "p" (el primLevel) $
       hPi "A" (return $ sort $ varSort 1) $
       hPi "x" (El (varSort 2) <$> varM 0) $
       nPi "C" (nPi "y" (El (varSort 3) <$> varM 1) $
                 (El (varSort 4) <$> primId <#> varM 4 <#> varM 2 <@> varM 1 <@> varM 0) --> return (sort $ varSort 3)) $
       (El (varSort 3) <$> varM 0 <@> varM 1 <@>
            (primConId <#> varM 4 <#> varM 2 <#> varM 1 <#> varM 1 <@> primIOne
                       <@> (primPathAbs <#> varM 4 <#> varM 2 <@> (pure $ lam_i (var 2))))) -->
       (hPi "y" (El (varSort 4) <$> varM 2) $
        nPi "p" (El (varSort 4) <$> primId <#> varM 5 <#> varM 3 <@> varM 2 <@> varM 0) $
        El (varSort 5) <$> varM 2 <@> varM 1 <@> varM 0)
  unview <- intervalUnview'
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 8 $ \ ts -> do
    case ts of
     [la,lc,a,x,c,d,y,eq] -> do
       seq <- reduceB' eq
       conidn <- getBuiltinName' builtinConId
       conid <- getBuiltin' builtinConId
       comp <- getPrimitiveTerm' "primComp"
       papply <- getPrimitiveTerm' "primPathApply"
       pabs   <- getBuiltin' builtinPathAbs
       case (comp, papply, conid, pabs, unArg $ ignoreBlocking $ seq) of
         (Just comp, Just papply, Just conid, Just pabs
          , Def q [Apply la,Apply a,Apply x,Apply y,Apply phi,Apply p]) | Just q == conidn -> do
          redReturn $ comp `apply`
             [lc
             ,argN $ Lam defaultArgInfo $ mkAbs "i" $ let
                  w = papply `apply` [la,a,x,y,p]
                  wi = raise 1 w `apply` [argN $ var 0]
                  pabs' t = pabs `apply` (map (raise 1) [la,a] ++ [argN t])
               in unArg (raise 1 c) `apply`
                        [argH $ wi
                        ,argN $ conid `apply` (map (raise 1) [la,a,x] ++ [argH wi] ++
                                                [argN $ unview (IMax (raise 1 phi) (argN $ unview (INeg (argN $ var 0))))
                                                ,argN $ pabs' $ Lam defaultArgInfo $ mkAbs "j" $ raise 2 w `apply`
                                                             [argN $ unview $ (IMin (argN $ var 1) (argN $ var 0))]])]
             ,argN $ unArg phi
             ,argN $ Lam defaultArgInfo $ mkAbs "i" $ unArg $ raise 1 d -- TODO cast to Partial, and block
             ,d]
         _ -> return $ NoReduction $ map notReduced [la,lc,a,x,c,d,y] ++ [reduced seq]
     _ -> __IMPOSSIBLE__

primPFrom1 :: TCM PrimitiveImpl
primPFrom1 = do
  t    <- hPi "a" (el primLevel) $
          hPi "A" (el primInterval --> (return $ sort $ varSort 0)) $
          (El (varSort 1) <$> varM 0 <@> intervalUnview IOne) -->
          (nPi "i" (el primInterval) $
           nPi "j" (el primInterval) $
          (El (varSort 3) <$> primPartial <#> varM 3 <@> (varM 2 <@>
             (intervalUnview =<< (\ i j -> IMax (argN i) (argN j)) <$> varM 1 <*> varM 0)) <@> varM 1))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,a,u,i,j] -> do
        si <- reduceB' i
        vi <- intervalView $ unArg $ ignoreBlocking $ si
        case vi of
          IOne -> redReturn (unArg u)
          _    -> do
            sj <- reduceB' j
            vj <- intervalView $ unArg $ ignoreBlocking $ sj
            case vj of
              IOne -> redReturn (unArg u)
              _    -> return $ NoReduction $ [notReduced l, notReduced a, notReduced u, reduced si, reduced sj]
      _         -> __IMPOSSIBLE__

primPOr :: TCM PrimitiveImpl
primPOr = do
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          nPi "i" (el primInterval) $
          nPi "j" (el primInterval) $
          (El (varSort 3) <$> primPartial <#> varM 3 <@> varM 2 <@> varM 1) -->
          (El (varSort 3) <$> primPartial <#> varM 3 <@> varM 2 <@> varM 0) -->
          (El (varSort 3) <$> primPartial <#> varM 3 <@> varM 2 <@>
           (intervalUnview =<< ((\ x y -> IMax (Arg defaultArgInfo x) (Arg defaultArgInfo y)) <$>
                                                                                               varM 1 <*> varM 0)))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 6 $ \ ts -> do
    case ts of
     [l,a,i,j,u,v] -> do
       si <- reduceB' i
       vi <- intervalView $ unArg $ ignoreBlocking si
       case vi of
        IOne -> redReturn (unArg u)
        _ -> do
          sj <- reduceB' j
          vj <- intervalView $ unArg $ ignoreBlocking sj
          case vj of
            IOne -> redReturn (unArg v)
            _ -> return $ NoReduction [notReduced l,notReduced a,reduced si,reduced sj,notReduced u,notReduced v]


     _ -> __IMPOSSIBLE__


primComp :: TCM PrimitiveImpl
primComp = do
  t    <- hPi "a" (el primLevel) $
          nPi "A" (el primInterval --> (return $ sort $ varSort 0)) $
          nPi "φ" (el primInterval) $
          (nPi "i" (el primInterval) $ El (varSort 3) <$> primPartial <#> varM 3 <@> (varM 2 <@> varM 0) <@> varM 1) -->
          ((El (varSort 2) <$> (varM 1 <@> primIZero)) --> (El (varSort 2) <$> (varM 1 <@> primIOne)))
  unview <- intervalUnview'
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,c,phi,u,a0] -> do
        sphi <- reduceB' phi
        vphi <- intervalView $ unArg $ ignoreBlocking sphi
        io   <- intervalUnview IOne
        case vphi of
          IOne -> redReturn (apply (unArg u) [Arg defaultArgInfo io])
          _    -> do
           sc <- reduceB' c
           case unArg $ ignoreBlocking sc of
             Lam _info t ->
               case unAbs t of
                 Pi a b   -> redReturn =<< compPi unview t a b (ignoreBlocking sphi) u a0 --  __IMPOSSIBLE__ -- Lam _ (comp (Lam
                 Sort s   | False -> __IMPOSSIBLE__ -- Glue guys
                 Def q es | False -> __IMPOSSIBLE__  -- Datatypes and primitives
                 _ -> return $ NoReduction [notReduced l,reduced sc, reduced sphi, notReduced u, notReduced a0]
             _ -> return $ NoReduction [notReduced l,reduced sc, reduced sphi, notReduced u, notReduced a0]
      _ -> __IMPOSSIBLE__
 where
  compPi :: (IntervalView -> Term) ->
            Abs Term -> Dom Type -> Abs Type -> -- Γ , i : I
               Arg Term -- phi -- Γ
            -> Arg Term -- u -- function -- Γ
            -> Arg Term -- λ0 -- fine -- Γ
            -> ReduceM Term
  compPi unview t a b phi u a0 = do
   tComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primComp"
   tFrom1 <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveTerm' "primPFrom1"
   let
    ineg t = (unview . INeg . argN) t
    imax u t = unview (IMax (argN u) (argN t))
    toLevel (Type l) = l
    toLevel _        = __IMPOSSIBLE__
    termComp = pure tComp
    v' = termComp <#> sa <@> (pure $ lam_j  -- Γ , u1 : A[i1] , i : I , j : I
                                           at)
                          <@> varM 0 -- Γ , u1 : A[i1] , i : I
                          <@> (lam_j <$> (pure tFrom1 <#> sa' <#> (pure $ lam_i $ unEl $ unDom a')
                                                     <@> pure (raise 2 u1) <@> varM 1 <@> (ineg <$> varM 0)))
                          <@> (pure $ raise 1 u1)
    u1 = var 0  -- Γ , u1 : A[i1]
    a' = applySubst (liftS 1 $ raiseS 3) a -- Γ , u1 : A[i1] , i : I , j : I , i' : I
    sa' = pure $ applySubst (strengthenS __IMPOSSIBLE__ 1) $ Level . toLevel $ getSort a'
    a'' = (applySubst (singletonS 0 iOrNj) a')
    sa = pure $ applySubst (strengthenS __IMPOSSIBLE__ 1) $ Level . toLevel $ getSort a''

    at = unEl . unDom $ a''

    iOrNj = var 1 `imax` (ineg $ var 0)  -- Γ , u1 : A[i1] , i : I , j : I
               -- Γ , u1 : A[i1] , i : I
    i0 = unview IZero
    lam = Lam defaultArgInfo
    lam_i m = lam (mkAbs (absName t) m)
    lam_j m = lam (mkAbs "j" m)
   v <- v'
   let
    b'  = unAbs $ b -- Γ , i : I , x : A[i]
    b''' = applySubst (consS v $ liftS 1 $ raiseS 1) b' -- Γ , u1 : A[i1] , i : I
    b'' = unEl b'''
    sb = pure $ applySubst (strengthenS __IMPOSSIBLE__ 1) $ Level . toLevel $ getSort b'''
   (Lam (getArgInfo a) . mkAbs (absName b)) <$>

     -- Γ , u1 : A[i1]
      (termComp <#> sb <@> pure (lam_i -- Γ , u1 : A[i1] , i : I
                                      b'')
                      <@> pure (raise 1 (unArg phi))
                      <@> (lam_i <$> -- Γ , u1 : A[i1] , i : I
                                  (gApply (getHiding a) (pure (raise 2 (unArg u)) <@> varM 0) (pure v))) -- block until φ = 1?
                      <@> (gApply (getHiding a) (pure $ raise 1 (unArg a0)) (subst 0 i0 <$> pure v))) -- Γ , u1 : A[i1]



-- trustMe : {a : Level} {A : Set a} {x y : A} -> x ≡ y
primTrustMe :: TCM PrimitiveImpl
primTrustMe = do
  clo <- commandLineOptions
  when (optSafe clo) (typeError SafeFlagPrimTrustMe)
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          hPi "x" (El (varSort 1) <$> varM 0) $
          hPi "y" (El (varSort 2) <$> varM 1) $
          El (varSort 3) <$>
            primEquality <#> varM 3 <#> varM 2 <@> varM 1 <@> varM 0
  Con rf [] <- ignoreSharing <$> primRefl
  n         <- conPars . theDef <$> getConInfo rf
  -- Andreas, 2015-02-27  Forced Big vs. Forced Small should not matter here
  let refl x | n == 2    = Con rf [setRelevance (Forced Small) $ hide $ defaultArg x]
             | n == 3    = Con rf []
             | otherwise = __IMPOSSIBLE__
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ts ->
      case ts of
        [a, t, u, v] -> do
            -- Andreas, 2013-07-22.
            -- Note that we cannot call the conversion checker here,
            -- because 'reduce' might be called in a context where
            -- some bound variables do not have a type (just 'Prop),
            -- and the conversion checker for eliminations does not
            -- like this.
            -- We can only do untyped equality, e.g., by normalisation.
            (u', v') <- normalise' (u, v)
            if u' == v' then redReturn (refl $ unArg u) else
              return (NoReduction $ map notReduced [a, t, u, v])
{- OLD:

              -- BAD:
              noConstraints $
                equalTerm (El (Type $ lvlView $ unArg a) (unArg t)) (unArg u) (unArg v)
              redReturn (refl $ unArg u)
            `catchError` \_ -> return (NoReduction $ map notReduced [a, t, u, v])
-}
        _ -> __IMPOSSIBLE__

-- Used for both primForce and primForceLemma.
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

(-->), (.-->), (..-->) :: TCM Type -> TCM Type -> TCM Type
a --> b = garr id a b
a .--> b = garr (const $ Irrelevant) a b
a ..--> b = garr (const $ NonStrict) a b

garr :: Monad tcm => (Relevance -> Relevance) -> tcm Type -> tcm Type -> tcm Type
garr f a b = do
  a' <- a
  b' <- b
  return $ El (getSort a' `sLub` getSort b') $
    Pi (Dom (mapRelevance f defaultArgInfo) a') (NoAbs "_" b')

gpi :: MonadTCM tcm => ArgInfo -> String -> tcm Type -> tcm Type -> tcm Type
gpi info name a b = do
  a <- a
  b <- addContext (name, Dom info a) b
  let y = stringToArgName name
  return $ El (getSort a `dLub` Abs y (getSort b))
              (Pi (Dom info a) (Abs y b))

hPi, nPi :: MonadTCM tcm => String -> tcm Type -> tcm Type -> tcm Type
hPi = gpi $ setHiding Hidden defaultArgInfo
nPi = gpi defaultArgInfo

varM :: Monad tcm => Int -> tcm Term
varM = return . var

infixl 9 <@>, <#>

gApply :: Monad tcm => Hiding -> tcm Term -> tcm Term -> tcm Term
gApply h a b = do
    x <- a
    y <- b
    return $ x `apply` [Arg (setHiding h defaultArgInfo) y]

(<@>),(<#>) :: Monad tcm => tcm Term -> tcm Term -> tcm Term
(<@>) = gApply NotHidden
(<#>) = gApply Hidden

list :: TCM Term -> TCM Term
list t = primList <@> t

io :: TCM Term -> TCM Term
io t = primIO <@> t

path :: TCM Term -> TCM Term
path t = primPath <@> t

el :: Monad tcm => tcm Term -> tcm Type
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
domN = Dom defaultArgInfo

-- | Abbreviation: @argH = 'hide' 'Arg' 'defaultArgInfo'@.
argH :: e -> Arg e
argH = Arg $ setHiding Hidden defaultArgInfo

domH :: e -> Dom e
domH = Dom $ setHiding Hidden defaultArgInfo

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
  , "primNatToFloat"      |-> mkPrimFun1 (fromIntegral :: Nat -> Double)
  , "primFloatPlus"       |-> mkPrimFun2 ((+)          :: Op Double)
  , "primFloatMinus"      |-> mkPrimFun2 ((-)          :: Op Double)
  , "primFloatTimes"      |-> mkPrimFun2 ((*)          :: Op Double)
  , "primFloatDiv"        |-> mkPrimFun2 ((/)          :: Op Double)
  , "primFloatEquality"   |-> mkPrimFun2 (floatEq      :: Rel Double)
  , "primFloatLess"       |-> mkPrimFun2 (floatLt      :: Rel Double)
  , "primFloatSqrt"       |-> mkPrimFun1 (sqrt         :: Double -> Double)
  , "primRound"           |-> mkPrimFun1 (round        :: Double -> Integer)
  , "primFloor"           |-> mkPrimFun1 (floor        :: Double -> Integer)
  , "primCeiling"         |-> mkPrimFun1 (ceiling      :: Double -> Integer)
  , "primExp"             |-> mkPrimFun1 (exp          :: Fun Double)
  , "primLog"             |-> mkPrimFun1 (log          :: Fun Double)
  , "primSin"             |-> mkPrimFun1 (sin          :: Fun Double)
  , "primShowFloat"       |-> mkPrimFun1 (Str . floatShow :: Double -> Str)

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
  , "primMetaEquality"    |-> mkPrimFun2 ((==) :: Rel MetaId)
  , "primMetaLess"        |-> mkPrimFun2 ((<) :: Rel MetaId)
  , "primShowMeta"        |-> mkPrimFun1 (Str . show . pretty :: MetaId -> Str)
  , "primPathApply"       |-> primPathApply
  , "primIMin"            |-> primIMin
  , "primIMax"            |-> primIMax
  , "primINeg"            |-> primINeg
  , "primCoe"             |-> primCoe
  , "primPOr"             |-> primPOr
  , "primComp"            |-> primComp
  , "primPFrom1"          |-> primPFrom1
  , "primOutPartial"      |-> primOutPartial
  , "primIdJ"             |-> primIdJ
  , "primPOr'"             |-> primPOr
  , "primComp'"            |-> primComp
  ]
  where
    (|->) = (,)


floatEq :: Double -> Double -> Bool
floatEq x y | isNaN x && isNaN y = True
            | otherwise          = x == y

floatLt :: Double -> Double -> Bool
floatLt x y
  | isNegInf y = False
  | isNegInf x = True
  | isNaN x    = True
  | otherwise  = x < y
  where
    isNegInf z = z < 0 && isInfinite z

floatShow :: Double -> String
floatShow x | isNegativeZero x = "0.0"
            | otherwise        = show x

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
  caseMaybeM (getBuiltin' b) (return Nothing) $ \v -> do
    v <- normalise v
    let getName (Def x _) = x
        getName (Con x _) = conName x
        getName (Lam _ b) = getName $ ignoreSharing $ unAbs b
        getName _         = __IMPOSSIBLE__
    return $ Just $ getName (ignoreSharing v)

isBuiltin :: QName -> String -> TCM Bool
isBuiltin q b = (Just q ==) <$> getBuiltinName b
