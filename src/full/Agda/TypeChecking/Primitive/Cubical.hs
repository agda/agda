{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}

module Agda.TypeChecking.Primitive.Cubical where

import Prelude hiding (null, (!!))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )
import Control.Exception

import Data.Typeable
import Data.String

import Data.Bifunctor ( second )
import Data.Either ( partitionEithers )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optCubical )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Maybe

import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple
import Agda.Utils.Size
import Agda.Utils.BoolSet (BoolSet)
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.BoolSet as BoolSet

-- | Checks that the correct variant of Cubical Agda is activated.
-- Note that @--erased-cubical@ \"counts as\" @--cubical@ in erased
-- contexts.

requireCubical
  :: Cubical -- ^ Which variant of Cubical Agda is required?
  -> String -> TCM ()
requireCubical wanted s = do
  cubical         <- optCubical <$> pragmaOptions
  inErasedContext <- hasQuantity0 <$> getEnv
  case cubical of
    Just CFull -> return ()
    Just CErased | wanted == CErased || inErasedContext -> return ()
    _ -> typeError $ GenericError $ "Missing option " ++ opt ++ s
  where
  opt = case wanted of
    CFull   -> "--cubical"
    CErased -> "--cubical or --erased-cubical"

primIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primIntervalType = El intervalSort <$> primInterval

primINeg' :: TCM PrimitiveImpl
primINeg' = do
  requireCubical CErased ""
  t <- primIntervalType --> primIntervalType
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
  requireCubical CErased ""
  t <- runNamesT [] $
       nPi' "φ" primIntervalType $ \ φ ->
       pPi' "o" φ (\ o -> primIntervalType) --> primIntervalType
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
  requireCubical CErased ""
  t <- primIntervalType --> primIntervalType --> primIntervalType
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
primIMin' = do
  requireCubical CErased ""
  primIBin IOne IZero

primIMax' :: TCM PrimitiveImpl
primIMax' = do
  requireCubical CErased ""
  primIBin IZero IOne

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
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "c" (el $ cl primLevel) $ \ c ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       nPi' "C" (nPi' "y" (el' a bA) $ \ y ->
                 el' a (cl primId <#> a <#> bA <@> x <@> y) --> (sort . tmSort <$> c)) $ \ bC ->
       el' c (bC <@> x <@>
            (cl primConId <#> a <#> bA <#> x <#> x <@> cl primIOne
                       <@> lam "i" (\ _ -> x))) -->
       hPi' "y" (el' a bA) (\ y ->
        nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
        el' c $ bC <@> y <@> p)
  conidn <- getName' builtinConId
  conid  <- primConId
  -- TODO make a kit
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ ts -> do
    unview <- intervalUnview'
    let imax x y = do x' <- x; unview . IMax (argN x') . argN <$> y;
        imin x y = do x' <- x; unview . IMin (argN x') . argN <$> y;
        ineg x = unview . INeg . argN <$> x
    mcomp <- getTerm' "primComp"
    case ts of
     [la,lc,a,x,c,d,y,eq] -> do
       seq    <- reduceB' eq
       cview <- conidView'
       case cview (unArg x) $ unArg $ ignoreBlocking $ seq of
         Just (phi,p)
           | Just comp <- mcomp -> do
          redReturn $ runNames [] $ do
             [lc,c,d,la,a,x,y,phi,p] <- mapM (open . unArg) [lc,c,d,la,a,x,y,phi,p]
             let w i = do
                   [x,y,p,i] <- sequence [x,y,p,i]
                   pure $ p `applyE` [IApply x y i]
             pure comp <#> lam "i" (\ _ -> lc)
                       <@> lam "i" (\ i ->
                              c <@> (w i)
                                <@> (pure conid <#> la <#> a <#> x <#> (w i)
                                                <@> (phi `imax` ineg i)
                                                <@> lam "j" (\ j -> w $ imin i j)))
                       <#> phi
                       <@> lam "i" (\ _ -> nolam <$> d) -- TODO block
                       <@> d
         _ -> return $ NoReduction $ map notReduced [la,lc,a,x,c,d,y] ++ [reduced seq]
     _ -> __IMPOSSIBLE__

primIdElim' :: TCM PrimitiveImpl
primIdElim' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "c" (el $ cl primLevel) $ \ c ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       nPi' "C" (nPi' "y" (el' a bA) $ \ y ->
                 el' a (cl primId <#> a <#> bA <@> x <@> y) --> (sort . tmSort <$> c)) $ \ bC ->
       nPi' "φ" primIntervalType (\ phi ->
        nPi' "y" (el's a $ cl primSub <#> a <@> bA <@> phi <@> lam "o" (const x)) $ \ y ->
        let pathxy = (cl primPath <#> a <@> bA <@> x <@> oucy)
            oucy = (cl primSubOut <#> a <#> bA <#> phi <#> lam "o" (const x) <@> y)
            reflx = (lam "o" $ \ _ -> lam "i" $ \ _ -> x) -- TODO Andrea, should block on o
        in
        nPi' "w" (el's a $ cl primSub <#> a <@> pathxy <@> phi <@> reflx) $ \ w ->
        let oucw = (cl primSubOut <#> a <#> pathxy <#> phi <#> reflx <@> w) in
        el' c $ bC <@> oucy <@> (cl primConId <#> a <#> bA <#> x <#> oucy <@> phi <@> oucw))
       -->
       hPi' "y" (el' a bA) (\ y ->
        nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
        el' c $ bC <@> y <@> p)
  conid <- primConId
  sin <- primSubIn
  path <- primPath
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ ts -> do
    case ts of
      [a,c,bA,x,bC,f,y,p] -> do
        sp <- reduceB' p
        cview <- conidView'
        case cview (unArg x) $ unArg $ ignoreBlocking sp of
          Just (phi , w) -> do
            let y' = sin `apply` [a,bA                            ,phi,argN $ unArg y]
            let w' = sin `apply` [a,argN $ path `apply` [a,bA,x,y],phi,argN $ unArg w]
            redReturn $ unArg f `apply` [phi, defaultArg y', defaultArg w']
          _ -> return $ NoReduction $ map notReduced [a,c,bA,x,bC,f,y] ++ [reduced sp]
      _ -> __IMPOSSIBLE__


primPOr :: TCM PrimitiveImpl
primPOr = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel)    $ \ a  ->
          nPi' "i" primIntervalType $ \ i  ->
          nPi' "j" primIntervalType $ \ j  ->
          hPi' "A" (pPi' "o" (imax i j) $ \o -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          ((pPi' "i1" i $ \ i1 -> el' a $ bA <..> (cl primIsOne1 <@> i <@> j <@> i1))) -->
          ((pPi' "j1" j $ \ j1 -> el' a $ bA <..> (cl primIsOne2 <@> i <@> j <@> j1))) -->
          pPi' "o" (imax i j) (\ o -> el' a $ bA <..> o)
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
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) (\ a ->
        nPi' "φ" primIntervalType $ \ _ ->
        nPi' "A" (sort . tmSort <$> a) $ \ bA ->
        (sort . tmSSort <$> a))
  isOne <- primIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 3 $ \ ts -> do
    case ts of
      [l,phi,a] -> do
          (El s (Pi d b)) <- runNamesT [] $ do
                             [l,a,phi] <- mapM (open . unArg) [l,a,phi]
                             elSSet (pure isOne <@> phi) --> el' l a
          redReturn $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      _ -> __IMPOSSIBLE__

primPartialP' :: TCM PrimitiveImpl
primPartialP' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) (\ a ->
        nPi' "φ" primIntervalType $ \ phi ->
        nPi' "A" (pPi' "o" phi $ \ _ -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
        (sort . tmSSort <$> a))
  let toFinitePi :: Type -> Term
      toFinitePi (El _ (Pi d b)) = Pi (setRelevance Irrelevant $ d { domFinite = True }) b
      toFinitePi _               = __IMPOSSIBLE__
  v <- runNamesT [] $
        lam "a" $ \ l ->
        lam "φ" $ \ phi ->
        lam "A" $ \ a ->
        toFinitePi <$> nPi' "p" (elSSet $ cl primIsOne <@> phi) (\ p -> el' l (a <@> p))
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v

primSubOut' :: TCM PrimitiveImpl
primSubOut' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          hPi' "u" (el's a $ cl primPartial <#> a <@> phi <@> bA) $ \ u ->
          el's a (cl primSub <#> a <@> bA <@> phi <@> u) --> el' a bA
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

primConId' :: TCM PrimitiveImpl
primConId' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       primIntervalType -->
       (el' a $ cl primPath <#> a <#> bA <@> x <@> y)
       --> (el' a $ cl primId <#> a <#> bA <@> x <@> y)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts -> do
    case ts of
      [l,bA,x,y,phi,p] -> do
        sphi <- reduceB' phi
        view <- intervalView'
        case view $ unArg $ ignoreBlocking sphi of
          IOne -> do
            reflId <- getTerm builtinConId builtinReflId
            redReturn $ reflId
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced sphi, notReduced p]
      _ -> __IMPOSSIBLE__

primIdFace' :: TCM PrimitiveImpl
primIdFace' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       el' a (cl primId <#> a <#> bA <@> x <@> y)
       --> primIntervalType
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        cview <- conidView'
        case cview (unArg x) $ unArg (ignoreBlocking st) of
          Just (phi,_) -> redReturn (unArg phi)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__

primIdPath' :: TCM PrimitiveImpl
primIdPath' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (el $ cl primLevel) $ \ a ->
       hPi' "A" (sort . tmSort <$> a) $ \ bA ->
       hPi' "x" (el' a bA) $ \ x ->
       hPi' "y" (el' a bA) $ \ y ->
       el' a (cl primId <#> a <#> bA <@> x <@> y)
       --> el' a (cl primPath <#> a <#> bA <@> x <@> y)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [l,bA,x,y,t] -> do
        st <- reduceB' t
        mConId <- getName' builtinConId
        cview <- conidView'
        case cview (unArg x) $ unArg (ignoreBlocking st) of
          Just (_,w)-> redReturn (unArg w)
          _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
      _ -> __IMPOSSIBLE__


primTrans' :: TCM PrimitiveImpl
primTrans' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (primIntervalType --> el (cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" primIntervalType $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          nPi' "φ" primIntervalType $ \ phi ->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ ts nelims -> do
    primTransHComp DoTransp ts nelims

primHComp' :: TCM PrimitiveImpl
primHComp' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (el $ cl primLevel) $ \ a ->
          hPi' "A" (sort . tmSort <$> a) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          nPi' "i" primIntervalType (\ i -> pPi' "o" phi $ \ _ -> el' a bA) -->
          (el' a bA --> el' a bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    primTransHComp DoHComp ts nelims

data TranspOrHComp = DoTransp | DoHComp deriving (Eq,Show)

cmdToName :: TranspOrHComp -> String
cmdToName DoTransp = builtinTrans
cmdToName DoHComp  = builtinHComp

data FamilyOrNot a
  = IsFam { famThing :: a }
  | IsNot { famThing :: a }
  deriving (Eq,Show,Functor,Foldable,Traversable)

familyOrNot :: IsString p => FamilyOrNot a -> p
familyOrNot (IsFam x) = "IsFam"
familyOrNot (IsNot x) = "IsNot"

instance Reduce a => Reduce (FamilyOrNot a) where
  reduceB' x = traverse id <$> traverse reduceB' x
  reduce' x = traverse reduce' x


mkComp :: HasBuiltins m => String -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkComp s = do
  let getTermLocal = getTerm s
  tComp <- getTermLocal builtinComp
  return $ \ la bA phi u u0 ->
    pure tComp <#> la
               <@> bA
               <#> phi
               <@> u
               <@> u0




-- | Define a "ghcomp" version of gcomp. Normal comp looks like:
--
-- comp^i A [ phi -> u ] u0 = hcomp^i A(1/i) [ phi -> forward A i u ] (forward A 0 u0)
--
-- So for "gcomp" we compute:
--
-- gcomp^i A [ phi -> u ] u0 = hcomp^i A(1/i) [ phi -> forward A i u, ~ phi -> forward A 0 u0 ] (forward A 0 u0)
--
-- The point of this is that gcomp does not produce any empty
-- systems (if phi = 0 it will reduce to "forward A 0 u".
mkGComp :: HasBuiltins m => String -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkGComp s = do
  let getTermLocal = getTerm s
  tPOr <- getTermLocal "primPOr"
  tIMax <- getTermLocal builtinIMax
  tIMin <- getTermLocal builtinIMin
  tINeg <- getTermLocal builtinINeg
  tHComp <- getTermLocal builtinHComp
  tTrans <- getTermLocal builtinTrans
  io      <- getTermLocal builtinIOne
  iz      <- getTermLocal builtinIZero
  let ineg j = pure tINeg <@> j
      imax i j = pure tIMax <@> i <@> j
  let forward la bA r u = pure tTrans <#> lam "i" (\ i -> la <@> (i `imax` r))
                                      <@> lam "i" (\ i -> bA <@> (i `imax` r))
                                      <@> r
                                      <@> u
  return $ \ la bA phi u u0 ->
    pure tHComp <#> (la <@> pure io)
                <#> (bA <@> pure io)
                <#> imax phi (ineg phi)
                <@> lam "i" (\ i ->
                      pure tPOr <#> (la <@> i)
                                <@> phi
                                <@> ineg phi
                                <@> ilam "o" (\ a -> bA <@> i)
                                <@> ilam "o" (\ o -> forward la bA i (u <@> i <..> o))
                                <@> ilam "o" (\ o -> forward la bA (pure iz) u0))
                <@> forward la bA (pure iz) u0


unglueTranspGlue :: PureTCM m =>
                  Arg Term
                  -> Arg Term
                  -> FamilyOrNot
                       (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
                  -> m Term
-- ...    |- psi, u0
-- ..., i |- la, lb, bA, phi, bT, e
unglueTranspGlue psi u0 (IsFam (la, lb, bA, phi, bT, e)) = do
      let
        localUse = builtinTrans ++ " for " ++ builtinGlue
        getTermLocal = getTerm localUse
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
      tTransp <- getTermLocal builtinTranspProof
      tItIsOne <- getTermLocal builtinItIsOne
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      runNamesT [] $ do
        let ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            imin i j = pure tIMin <@> i <@> j

        gcomp <- mkGComp localUse

        let transpFill la bA phi u0 i =
              pure tTrans <#> lam "j" (\ j -> la <@> imin i j)
                          <@> lam "j" (\ j -> bA <@> imin i j)
                          <@> (imax phi (ineg i))
                          <@> u0
        [psi,u0] <- mapM (open . unArg) [psi,u0]

        -- glue1 t a = glue la[i1/i] lb[i1/i] bA[i1/i] phi[i1/i] bT[i1/i] e[i1/i] t a
        glue1 <- do
          g <- open $ (tglue `apply`) . map ((setHiding Hidden) . (subst 0 io)) $ [la, lb, bA, phi, bT, e]
          return $ \ t a -> g <@> t <@> a

        [la, lb, bA, phi, bT, e] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [la, lb, bA, phi, bT, e]

        -- Andreas, 2022-03-24, fixing #5838
        -- Following the updated note
        --
        --   Simon Huber, A Cubical Type Theory for Higher Inductive Types
        --   https://simhu.github.io/misc/hcomp.pdf (February 2022)
        --
        -- See: https://github.com/agda/agda/issues/5755#issuecomment-1043797776

        -- unglue_u0 i = unglue la[i/i] lb[i/i] bA[i/i] phi[i/i] bT[i/i] e[i/i] u0
        let unglue_u0 i =
              foldl (<#>) (pure tunglue) (map (<@> i) [la, lb, bA, phi, bT, e]) <@> u0

        view <- intervalView'

        let
          tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <..> o) psi u0 i
          t1 o = tf (pure io) o

          -- compute "forall. phi"
          forallphi = pure tForall <@> phi

          -- a1 with gcomp
          a1 = gcomp la bA
                 (imax psi forallphi)
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i)
                                             <@> psi
                                             <@> forallphi
                                             <@> ilam "o" (\ a -> bA <@> i)
                                             <@> ilam "o" (\ _ -> unglue_u0 i)
                                             <@> ilam "o" (\ o -> pure tEFun <#> (lb <@> i)
                                                                               <#> (la <@> i)
                                                                               <#> (bT <@> i <..> o)
                                                                               <#> (bA <@> i)
                                                                               <@> (e <@> i <..> o)
                                                                               <@> (tf i o)))
                 (unglue_u0 (pure iz))

          max l l' = pure tLMax <@> l <@> l'
          sigCon x y = pure (Con (sigmaCon kit) ConOSystem []) <@> x <@> y
          w i o = pure tEFun <#> (lb <@> i)
                             <#> (la <@> i)
                             <#> (bT <@> i <..> o)
                             <#> (bA <@> i)
                             <@> (e <@> i <..> o)
          fiber la lb bA bB f b =
            (pure (Def (sigmaName kit) []) <#> la
                                           <#> lb
                                           <@> bA
                                           <@> lam "a" (\ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b))

          -- We don't have to do anything special for "~ forall. phi"
          -- here (to implement "ghcomp") as it is taken care off by
          -- tEProof in t1'alpha below
          pe o = -- o : [ φ 1 ]
            pure tPOr <#> max (la <@> pure io) (lb <@> pure io)
                      <@> psi
                      <@> forallphi
                      <@> ilam "o" (\ _ ->
                             fiber (lb <@> pure io) (la <@> pure io)
                                   (bT <@> (pure io) <..> o) (bA <@> pure io)
                                   (w (pure io) o) a1)
                      <@> ilam "o" (\ o -> sigCon u0 (lam "_" $ \ _ -> a1))
                      <@> ilam "o" (\ o -> sigCon (t1 o) (lam "_" $ \ _ -> a1))

          -- "ghcomp" is implemented in the proof of tEProof
          -- (see src/data/lib/prim/Agda/Builtin/Cubical/Glue.agda)
          t1'alpha o = -- o : [ φ 1 ]
             pure tEProof <#> (lb <@> pure io)
                          <#> (la <@> pure io)
                          <@> (bT <@> pure io <..> o)
                          <@> (bA <@> pure io)
                          <@> (e <@> pure io <..> o)
                          <@> a1
                          <@> (imax psi forallphi)
                          <@> pe o

          -- TODO: optimize?
          t1' o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
          alpha o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaSnd kit)])
          a1' = pure tHComp
                  <#> (la <@> pure io)
                  <#> (bA <@> pure io)
                  <#> (imax (phi <@> pure io) psi)
                  <@> lam "j" (\ j ->
                         pure tPOr <#> (la <@> pure io) <@> (phi <@> pure io) <@> psi <@> ilam "o" (\ _ -> bA <@> pure io)
                                   <@> ilam "o" (\ o -> alpha o <@@> (w (pure io) o <@> t1' o,a1,j))
                                   <@> ilam "o" (\ _ -> a1))
                  <@> a1
        -- glue1 (ilam "o" t1') a1'
        a1'
unglueTranspGlue _ _ _ = __IMPOSSIBLE__

data TermPosition = Head | Eliminated deriving (Eq,Show)

headStop :: PureTCM m => TermPosition -> m Term -> m Bool
headStop tpos phi
  | Head <- tpos = do
      phi <- intervalView =<< (reduce =<< phi)
      return $ not $ isIOne phi
  | otherwise = return False

compGlue :: PureTCM m =>
                  TranspOrHComp
                  -> Arg Term
                  -> Maybe (Arg Term)
                  -> Arg Term
                  -> FamilyOrNot
                       (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
                  -> TermPosition
                  -> m (Maybe Term)
compGlue DoHComp psi (Just u) u0 (IsNot (la, lb, bA, phi, bT, e)) tpos = do
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
      tItIsOne <- getTermLocal builtinItIsOne
      view <- intervalView'
      runNamesT [] $ do
        [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]
        [la, lb, bA, phi, bT, e] <- mapM (open . unArg) [la, lb, bA, phi, bT, e]
        ifM (headStop tpos phi) (return Nothing) $ Just <$> do

        let
          hfill la bA phi u u0 i = pure tHComp <#> la
                                               <#> bA
                                               <#> (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               <@> lam "j" (\ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <@> ilam "o" (\ a -> bA)
                                                     <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> ilam "o" (\ _ -> u0))
                                               <@> u0
          tf i o = hfill lb (bT <..> o) psi u u0 i
          unglue g = pure tunglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> g
          a1 = pure tHComp <#> la <#> bA <#> (pure tIMax <@> psi <@> phi)
                           <@> lam "i" (\ i -> pure tPOr <#> la <@> psi <@> phi <@> ilam "_" (\ _ -> bA)
                                 <@> ilam "o" (\ o -> unglue (u <@> i <..> o))
                                 <@> ilam "o" (\ o -> pure tEFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o) <@> tf i o))
                           <@> (unglue u0)
          t1 = tf (pure io)
        -- pure tglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> (ilam "o" $ \ o -> t1 o) <@> a1
        case tpos of
          Head -> t1 (pure tItIsOne)
          Eliminated -> a1

-- ...    |- psi, u0
-- ..., i |- la, lb, bA, phi, bT, e
compGlue DoTransp psi Nothing u0 (IsFam (la, lb, bA, phi, bT, e)) tpos = do
      let
        localUse = builtinTrans ++ " for " ++ builtinGlue
        getTermLocal = getTerm localUse
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
      tTransp <- getTermLocal builtinTranspProof
      tItIsOne <- getTermLocal builtinItIsOne
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      runNamesT [] $ do
        let ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            imin i j = pure tIMin <@> i <@> j

        gcomp <- mkGComp localUse

        let transpFill la bA phi u0 i =
              pure tTrans <#> lam "j" (\ j -> la <@> imin i j)
                          <@> lam "j" (\ j -> bA <@> imin i j)
                          <@> (imax phi (ineg i))
                          <@> u0
        [psi,u0] <- mapM (open . unArg) [psi,u0]

        -- glue1 t a = glue la[i1/i] lb[i1/i] bA[i1/i] phi[i1/i] bT[i1/i] e[i1/i] t a
        glue1 <- do
          g <- open $ (tglue `apply`) . map ((setHiding Hidden) . (subst 0 io)) $ [la, lb, bA, phi, bT, e]
          return $ \ t a -> g <@> t <@> a

        [la, lb, bA, phi, bT, e] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [la, lb, bA, phi, bT, e]

        -- Andreas, 2022-03-24, fixing #5838
        -- Following the updated note
        --
        --   Simon Huber, A Cubical Type Theory for Higher Inductive Types
        --   https://simhu.github.io/misc/hcomp.pdf (February 2022)
        --
        -- See: https://github.com/agda/agda/issues/5755#issuecomment-1043797776

        -- unglue_u0 i = unglue la[i/i] lb[i/i] bA[i/i] phi[i/i] bT[i/i] e[i/e] u0
        let unglue_u0 i =
              foldl (<#>) (pure tunglue) (map (<@> i) [la, lb, bA, phi, bT, e]) <@> u0

        view <- intervalView'

        ifM (headStop tpos (phi <@> pure io)) (return Nothing) $ Just <$> do
        let
          tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <..> o) psi u0 i
          t1 o = tf (pure io) o

          -- compute "forall. phi"
          forallphi = pure tForall <@> phi

          -- a1 with gcomp
          a1 = gcomp la bA
                 (imax psi forallphi)
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i)
                                             <@> psi
                                             <@> forallphi
                                             <@> ilam "o" (\ _ -> bA <@> i)
                                             <@> ilam "o" (\ _ -> unglue_u0 i)
                                             <@> ilam "o" (\ o -> pure tEFun <#> (lb <@> i)
                                                                               <#> (la <@> i)
                                                                               <#> (bT <@> i <..> o)
                                                                               <#> (bA <@> i)
                                                                               <@> (e <@> i <..> o)
                                                                               <@> (tf i o)))
                 (unglue_u0 (pure iz))

          max l l' = pure tLMax <@> l <@> l'
          sigCon x y = pure (Con (sigmaCon kit) ConOSystem []) <@> x <@> y
          w i o = pure tEFun <#> (lb <@> i)
                             <#> (la <@> i)
                             <#> (bT <@> i <..> o)
                             <#> (bA <@> i)
                             <@> (e <@> i <..> o)
          fiber la lb bA bB f b =
            (pure (Def (sigmaName kit) []) <#> la
                                           <#> lb
                                           <@> bA
                                           <@> lam "a" (\ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b))

          -- We don't have to do anything special for "~ forall. phi"
          -- here (to implement "ghcomp") as it is taken care off by
          -- tEProof in t1'alpha below
          pe o = -- o : [ φ 1 ]
            pure tPOr <#> max (la <@> pure io) (lb <@> pure io)
                      <@> psi
                      <@> forallphi
                      <@> ilam "o" (\ _ ->
                             fiber (lb <@> pure io) (la <@> pure io)
                                   (bT <@> (pure io) <..> o) (bA <@> pure io)
                                   (w (pure io) o) a1)
                      <@> ilam "o" (\ o -> sigCon u0 (lam "_" $ \ _ -> a1))
                      <@> ilam "o" (\ o -> sigCon (t1 o) (lam "_" $ \ _ -> a1))

          -- "ghcomp" is implemented in the proof of tEProof
          -- (see src/data/lib/prim/Agda/Builtin/Cubical/Glue.agda)
          t1'alpha o = -- o : [ φ 1 ]
             pure tEProof <#> (lb <@> pure io)
                          <#> (la <@> pure io)
                          <@> (bT <@> pure io <..> o)
                          <@> (bA <@> pure io)
                          <@> (e <@> pure io <..> o)
                          <@> a1
                          <@> (imax psi forallphi)
                          <@> pe o

          -- TODO: optimize?
          t1' o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
          alpha o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaSnd kit)])
          a1' = pure tHComp
                  <#> (la <@> pure io)
                  <#> (bA <@> pure io)
                  <#> (imax (phi <@> pure io) psi)
                  <@> lam "j" (\ j ->
                         pure tPOr <#> (la <@> pure io) <@> (phi <@> pure io) <@> psi <@> ilam "o" (\ _ -> bA <@> pure io)
                                   <@> ilam "o" (\ o -> alpha o <@@> (w (pure io) o <@> t1' o,a1,j))
                                   <@> ilam "o" (\ _ -> a1))
                  <@> a1

        -- glue1 (ilam "o" t1') a1'
        case tpos of
          Head -> t1' (pure tItIsOne)
          Eliminated -> a1'
compGlue cmd phi u u0 _ _ = __IMPOSSIBLE__

compHCompU :: PureTCM m =>
                    TranspOrHComp
                    -> Arg Term
                    -> Maybe (Arg Term)
                    -> Arg Term
                    -> FamilyOrNot (Arg Term, Arg Term, Arg Term, Arg Term)
                    -> TermPosition
                    -> m (Maybe Term)

compHCompU DoHComp psi (Just u) u0 (IsNot (la, phi, bT, bA)) tpos = do
      let getTermLocal = getTerm $ (builtinHComp ++ " for " ++ builtinHComp ++ " of Set")
      io      <- getTermLocal builtinIOne
      iz      <- getTermLocal builtinIZero
      tPOr <- getTermLocal "primPOr"
      tIMax <- getTermLocal builtinIMax
      tIMin <- getTermLocal builtinIMin
      tINeg <- getTermLocal builtinINeg
      tHComp <- getTermLocal builtinHComp
      tTransp  <- getTermLocal builtinTrans
      tglue   <- getTermLocal builtin_glueU
      tunglue <- getTermLocal builtin_unglueU
      tLSuc   <- getTermLocal builtinLevelSuc
      tSubIn <- getTermLocal builtinSubIn
      tItIsOne <- getTermLocal builtinItIsOne
      runNamesT [] $ do
        [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]
        [la, phi, bT, bA] <- mapM (open . unArg) [la, phi, bT, bA]

        ifM (headStop tpos phi) (return Nothing) $ Just <$> do

        let
          hfill la bA phi u u0 i = pure tHComp <#> la
                                               <#> bA
                                               <#> (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               <@> lam "j" (\ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <@> ilam "o" (\ _ -> bA)
                                                     <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> ilam "o" (\ _ -> u0))
                                               <@> u0
          transp la bA a0 = pure tTransp <#> lam "i" (const la) <@> lam "i" bA <@> pure iz <@> a0
          tf i o = hfill la (bT <@> pure io <..> o) psi u u0 i
          bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
          unglue g = pure tunglue <#> la <#> phi <#> bT <#> bAS <@> g
          a1 = pure tHComp <#> la <#> bA <#> (pure tIMax <@> psi <@> phi)
                           <@> lam "i" (\ i -> pure tPOr <#> la <@> psi <@> phi <@> ilam "_" (\ _ -> bA)
                                 <@> ilam "o" (\ o -> unglue (u <@> i <..> o))
                                 <@> ilam "o" (\ o -> transp la (\ i -> bT <@> (pure tINeg <@> i) <..> o) (tf i o)))
                           <@> unglue u0
          t1 = tf (pure io)

        -- pure tglue <#> la <#> phi <#> bT <#> bAS <@> (ilam "o" $ \ o -> t1 o) <@> a1
        case tpos of
          Eliminated -> a1
          Head       -> t1 (pure tItIsOne)



compHCompU DoTransp psi Nothing u0 (IsFam (la, phi, bT, bA)) tpos = do
      let
        localUse = builtinTrans ++ " for " ++ builtinHComp ++ " of Set"
        getTermLocal = getTerm localUse
      tPOr <- getTermLocal "primPOr"
      tIMax <- getTermLocal builtinIMax
      tIMin <- getTermLocal builtinIMin
      tINeg <- getTermLocal builtinINeg
      tHComp <- getTermLocal builtinHComp
      tTrans <- getTermLocal builtinTrans
      tTranspProof <- getTermLocal builtinTranspProof
      tSubIn <- getTermLocal builtinSubIn
      tForall  <- getTermLocal builtinFaceForall
      io      <- getTermLocal builtinIOne
      iz      <- getTermLocal builtinIZero
      tLSuc   <- getTermLocal builtinLevelSuc
      tPath   <- getTermLocal builtinPath
      tItIsOne   <- getTermLocal builtinItIsOne
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      runNamesT [] $ do
        let ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            imin i j = pure tIMin <@> i <@> j
            transp la bA a0 = pure tTrans <#> lam "i" (const la) <@> lam "i" bA <@> pure iz <@> a0

        gcomp <- mkGComp localUse

        let transpFill la bA phi u0 i =
              pure tTrans <#> ilam "j" (\ j -> la <@> imin i j)
                          <@> ilam "j" (\ j -> bA <@> imin i j)
                          <@> (imax phi (ineg i))
                          <@> u0
        [psi,u0] <- mapM (open . unArg) [psi,u0]
        glue1 <- do
          tglue   <- cl $ getTermLocal builtin_glueU
          [la, phi, bT, bA] <- mapM (open . unArg . subst 0 io) $ [la, phi, bT, bA]
          let bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
          g <- (open =<<) $ pure tglue <#> la <#> phi <#> bT <#> bAS
          return $ \ t a -> g <@> t <@> a

        [la, phi, bT, bA] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [la, phi, bT, bA]

        -- Andreas, 2022-03-25, issue #5838.
        -- Port the fix of @unglueTranspGlue@ and @compGlue DoTransp@
        -- also to @compHCompU DoTransp@, as suggested by Tom Jack and Anders Mörtberg.
        -- We define @unglue_u0 i@ that is first used with @i@ and then with @i0@.
        -- The original code used it only with @i0@.
        tunglue <- cl $ getTermLocal builtin_unglueU
        let bAS i =
              pure tSubIn  <#> (pure tLSuc <@> (la <@> i))
                           <#> (Sort . tmSort <$> (la <@> i))
                           <#> (phi <@> i)
                           <@> (bA <@> i)
        let unglue_u0 i =
              pure tunglue <#> (la <@> i)
                           <#> (phi <@> i)
                           <#> (bT <@> i)
                           <#> bAS i
                           <@> u0

        ifM (headStop tpos (phi <@> pure io)) (return Nothing) $ Just <$> do

        let
          lb = la
          tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <@> pure io <..> o) psi u0 i
          t1 o = tf (pure io) o

          -- compute "forall. phi"
          forallphi = pure tForall <@> phi

          -- a1 with gcomp
          a1 = gcomp la bA
                 (imax psi forallphi)
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i)
                                             <@> psi
                                             <@> forallphi
                                             <@> ilam "o" (\ _ -> bA <@> i)
                                             <@> ilam "o" (\ _ -> unglue_u0 i)
                                             <@> ilam "o" (\ o -> transp (la <@> i)
                                                                           (\ j -> bT <@> i <@> ineg j <..> o)
                                                                           (tf i o)))
                 (unglue_u0 (pure iz))

          w i o = lam "x" $
                  transp (la <@> i)
                         (\ j -> bT <@> i <@> ineg j <..> o)

          pt o = -- o : [ φ 1 ]
            pure tPOr <#> (la <@> pure io)
                      <@> psi
                      <@> forallphi
                      <@> ilam "o" (\ _ -> bT <@> pure io <@> pure io <..> o)
                      <@> ilam "o" (\ o -> u0)
                      <@> ilam "o" (\ o -> t1 o)

          -- "ghcomp" is implemented in the proof of tTranspProof
          -- (see src/data/lib/prim/Agda/Builtin/Cubical/HCompU.agda)
          t1'alpha o = -- o : [ φ 1 ]
             pure tTranspProof <#> (la <@> pure io)
                               <@> lam "i" (\ i -> bT <@> pure io <@> ineg i <..> o)
                               <@> imax psi forallphi
                               <@> pt o
                               <@> (pure tSubIn <#> (la <@> pure io) <#> (bA <@> pure io)
                                                <#> imax psi forallphi
                                                <@> a1)

          -- TODO: optimize?
          t1' o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
          alpha o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaSnd kit)])
          a1' = pure tHComp
                  <#> (la <@> pure io)
                  <#> (bA <@> pure io)
                  <#> (imax (phi <@> pure io) psi)
                  <@> lam "j" (\ j ->
                         pure tPOr <#> (la <@> pure io) <@> (phi <@> pure io) <@> psi <@> ilam "o" (\ _ -> bA <@> pure io)
                                   <@> ilam "o" (\ o -> alpha o <@@> (w (pure io) o <@> t1' o,a1,j))
                                   <@> ilam "o" (\ _ -> a1))
                  <@> a1

        -- glue1 (ilam "o" t1') a1'
        case tpos of
          Eliminated -> a1'
          Head       -> t1' (pure tItIsOne)
compHCompU _ psi _ u0 _ _ = __IMPOSSIBLE__


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
                                                                   <#> ilam "o" (\ _ -> c)
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
               mHComp <- getPrimitiveName' builtinHComp
               mGlue <- getPrimitiveName' builtinGlue
               mId   <- getBuiltinName' builtinId
               pathV <- pathView'
               case famThing t of
                 MetaV m _ -> fallback' (fmap famThing $ blocked_ m *> sbA)
                 -- absName t instead of "i"
                 Pi a b | nelims > 0  -> maybe fallback redReturn =<< compPi cmd "i" ((a,b) <$ t) (ignoreBlocking sphi) u u0
                        | otherwise -> fallback

                 Sort (Type l) | DoTransp <- cmd -> compSort cmd fallback phi u u0 (l <$ t)

                 Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
                   maybe fallback redReturn =<< compGlue cmd phi u u0 ((la, lb, bA, phi', bT, e) <$ t) Head

                 Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
                   | Just q == mHComp, Sort (Type la) <- unArg s  -> do
                   maybe fallback redReturn =<< compHCompU cmd phi u u0 ((Level la <$ s, phi', bT, bA) <$ t) Head

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

                         | Just as <- allApplyElims es, [] <- recFields r -> compData Nothing False (recPars r) cmd l (as <$ t) sbA sphi u u0
                     Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons, dataTransp = mtrD}
                       | and [null pcons && ixs == 0 | DoHComp  <- [cmd]], Just as <- allApplyElims es ->
                         compData mtrD ((not $ null $ pcons) || ixs > 0) (pars+ixs) cmd l (as <$ t) sbA sphi u u0
                     Axiom constTransp | constTransp, [] <- es, DoTransp <- cmd -> redReturn $ unArg u0
                     _          -> fallback

                 _ -> fallback
  where
    compSort DoTransp fallback phi Nothing u0 (IsFam l) = do
      -- TODO should check l is constant
      redReturn $ unArg u0
    -- compSort DoHComp fallback phi (Just u) u0 (IsNot l) = -- hcomp for Set is a whnf, handled above.
    compSort _ fallback phi u u0 _ = __IMPOSSIBLE__
    compPi :: TranspOrHComp -> ArgName -> FamilyOrNot (Dom Type, Abs Type) -- Γ , i : I
            -> Arg Term -- Γ
            -> Maybe (Arg Term) -- Γ
            -> Arg Term -- Γ
            -> ReduceM (Maybe Term)
    compPi cmd t ab phi u u0 = do
     let getTermLocal = getTerm $ cmdToName cmd ++ " for function types"

     tTrans <- getTermLocal builtinTrans
     tHComp <- getTermLocal builtinHComp
     tINeg <- getTermLocal builtinINeg
     tIMax <- getTermLocal builtinIMax
     iz    <- getTermLocal builtinIZero
     let
      toLevel' t = do
        s <- reduce $ getSort t
        case s of
          (Type l) -> return (Just l)
          _        -> return Nothing
      toLevel t = fromMaybe __IMPOSSIBLE__ <$> toLevel' t
     -- make sure the codomain has a level.
     caseMaybeM (toLevel' . absBody . snd . famThing $ ab) (return Nothing) $ \ _ -> do
     runNamesT [] $ do
      labA <- do
        let (x,f) = case ab of
              IsFam (a,_) -> (a, \ a -> runNames [] $ lam "i" (const (pure a)))
              IsNot (a,_) -> (a, id)
        s <- reduce $ getSort x
        case s of
          Type lx -> do
            [la,bA] <- mapM (open . f) [Level lx, unEl . unDom $ x]
            pure $ Just $ \ iOrNot phi a0 -> pure tTrans <#> lam "j" (\ j -> la <@> iOrNot j)
                                                         <@> lam "j" (\ j -> bA <@> iOrNot j)
                                                         <@> phi
                                                         <@> a0
          LockUniv -> return $ Just $ \ _ _ a0 -> a0
          IntervalUniv -> do
            x' <- reduceB $ unDom x
            mInterval <- getBuiltinName' builtinInterval
            case unEl $ ignoreBlocking x' of
              Def q [] | Just q == mInterval -> return $ Just $ \ _ _ a0 -> a0
              _ -> return Nothing
          _ -> return Nothing

      caseMaybe labA (return Nothing) $ \ trA -> Just <$> do
      [phi, u0] <- mapM (open . unArg) [phi, u0]
      u <- traverse open (unArg <$> u)

      glam (getArgInfo (fst $ famThing ab)) (absName $ snd $ famThing ab) $ \ u1 -> do
        case (cmd, ab, u) of
          (DoHComp, IsNot (a , b), Just u) -> do
            bT <- (raise 1 b `absApp`) <$> u1
            let v = u1
            pure tHComp <#> (Level <$> toLevel bT)
                        <#> pure (unEl                      $ bT)
                        <#> phi
                        <@> lam "i" (\ i -> ilam "o" $ \ o -> gApply (getHiding a) (u <@> i <..> o) v)
                        <@> (gApply (getHiding a) u0 v)
          (DoTransp, IsFam (a , b), Nothing) -> do
            let v i = do
                       let
                         iOrNot j = pure tIMax <@> i <@> (pure tINeg <@> j)
                       trA iOrNot (pure tIMax <@> phi <@> i)
                                  u1
                -- Γ , u1 : A[i1] , i : I
                bB v = consS v (liftS 1 $ raiseS 1) `applySubst` (absBody b {- Γ , i : I , x : A[i] -})
                tLam = Lam defaultArgInfo
            bT <- bind "i" $ \ x -> fmap bB . v $ x
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
                       <@> lam "i'" (\ i ->
                            let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i)
                            in or phi (ineg j `imax` j)
                                          <@> ilam "o" (\ o -> u <@> i <..> o <@@> (x, y, j)) -- a0 <@@> (x <@> i, y <@> i, j)
                                          <@> (or (ineg j) j <@> ilam "_" (const x)
                                                                  <@> ilam "_" (const y)))
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
        let forward la bA r u = pure tTrans <#> lam "i" (\ i -> la <@> (i `imax` r))
                                            <@> lam "i" (\ i -> bA <@> (i `imax` r))
                                            <@> r
                                            <@> u
        return $ \ la bA phi u u0 ->
          pure tHComp <#> (la <@> pure io)
                      <#> (bA <@> pure io)
                      <#> phi
                      <@> lam "i" (\ i -> ilam "o" $ \ o ->
                              forward la bA i (u <@> i <..> o))
                      <@> forward la bA (pure iz) u0
      redReturn . runNames [] $ do
        [l,u0] <- mapM (open . unArg) [l,u0]
        phi      <- open . unArg . ignoreBlocking $ sphi
        [bA, x, y] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]
        lam "j" $ \ j ->
          comp l (lam "i" $ \ i -> bA <@> i <@> j) (phi `imax` (ineg j `imax` j))
                      (lam "i'" $ \ i ->
                            let or f1 f2 = pure tOr <#> l <@> f1 <@> f2 <#> lam "_" (\ _ -> bA <@> i <@> j) in
                                       or phi (ineg j `imax` j)
                                          <@> ilam "o" (\ o -> u0 <@@> (x <@> pure iz, y <@> pure iz, j))
                                          <@> (or (ineg j) j <@> ilam "_" (const (x <@> i))
                                                                  <@> ilam "_" (const (y <@> i))))
                      (u0 <@@> (x <@> pure iz, y <@> pure iz, j))
    compPathP _ sphi u a0 _ _ = __IMPOSSIBLE__
    compId cmd sphi u a0 l bA_x_y = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for " ++ builtinId
      unview <- intervalUnview'
      mConId <- getName' builtinConId
      cview <- conidView'
      let isConId t = isJust $ cview __DUMMY_TERM__ t
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
          tConId <- getTermLocal builtinConId
          runNamesT [] $ do
            let io = pure $ unview IOne
                iz = pure $ unview IZero
                conId = pure $ tConId
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
                IsFam (bA,x,y) -> mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]
                IsNot (bA,x,y) -> forM [bA,x,y] $ \ a -> open (Lam defaultArgInfo $ NoAbs "_" $ unArg a)
            let
              eval DoTransp l bA phi _ u0 = pure tTrans <#> l <@> bA <@> phi <@> u0
              eval DoHComp l bA phi u u0 = pure tHComp <#> (l <@> io) <#> (bA <@> io) <#> phi
                                                       <@> u <@> u0
            conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
                  <@> (pure tIMin <@> phi
                                  <@> ilam "o" (\ o -> pure tFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
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
            andM . for as $ \ (bs,ts) -> do
                 let u' = listS (IntMap.toAscList $ IntMap.map boolToI bs) `applySubst` u
                 t <- reduce2Lam u'
                 return $! p $ ignoreBlocking t
    reduce2Lam t = do
          t <- reduce' t
          case lam2Abs Relevant t of
            t -> underAbstraction_ t $ \ t -> do
               t <- reduce' t
               case lam2Abs Irrelevant t of
                 t -> underAbstraction_ t reduceB'
         where
           lam2Abs rel (Lam _ t) = absBody t <$ t
           lam2Abs rel t         = Abs "y" (raise 1 t `apply` [setRelevance rel $ argN $ var 0])
    allComponentsBack unview phi u p = do
            let
              boolToI b = if b then unview IOne else unview IZero
              lamlam t = Lam defaultArgInfo (Abs "i" (Lam (setRelevance Irrelevant defaultArgInfo) (Abs "o" t)))
            as <- decomposeInterval phi
            (flags,t_alphas) <- fmap unzip . forM as $ \ (bs,ts) -> do
                 let u' = listS bs' `applySubst` u
                     bs' = IntMap.toAscList $ IntMap.map boolToI bs
                     -- Γ₁, i : I, Γ₂, j : I, Γ₃  ⊢ weaken : Γ₁, Γ₂, Γ₃   for bs' = [(j,_),(i,_)]
                     -- ordering of "j,i,.." matters.
                 let weaken = foldr (\ j s -> s `composeS` raiseFromS j 1) idS (map fst bs')
                 t <- reduce2Lam u'
                 return $ (p $ ignoreBlocking t, listToMaybe [ (weaken `applySubst` (lamlam <$> t),bs) | null ts ])
            return $ (flags,t_alphas)
    compData mtrD False _ cmd@DoHComp (IsNot l) (IsNot ps) fsc sphi (Just u) a0 = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"

      let sc = famThing <$> fsc
      tEmpty <- getTermLocal builtinIsOneEmpty
      tPOr   <- getTermLocal builtinPOr
      iO   <- getTermLocal builtinIOne
      iZ   <- getTermLocal builtinIZero
      tMin <- getTermLocal builtinIMin
      tNeg <- getTermLocal builtinINeg
      let iNeg t = tNeg `apply` [argN t]
          iMin t u = tMin `apply` [argN t, argN u]
          iz = pure iZ
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
          a0 = f sa0
          isLit t@(Lit lt) = Just t
          isLit _ = Nothing
          isCon (Con h _ _) = Just h
          isCon _           = Nothing
          combine l ty d [] = d
          combine l ty d [(psi,u)] = u
          combine l ty d ((psi,u):xs)
            = pure tPOr <#> l <@> psi <@> foldr (imax . fst) iz xs
                        <#> ilam "o" (\ _ -> ty) -- the type
                        <@> u <@> (combine l ty d xs)
          noRed' su = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
            where
              su' = case view phi of
                     IZero -> notBlocked $ argN $ runNames [] $ do
                                 [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                                 lam "i" $ \ i -> pure tEmpty <#> l
                                                              <#> ilam "o" (\ _ -> c)
                     _     -> su
          sameConHeadBack Nothing Nothing su k = noRed' su
          sameConHeadBack lt h su k = do
            let u = unArg . ignoreBlocking $ su
            (b, ts) <- allComponentsBack unview phi u $ \ t ->
                        (isLit t == lt, isCon (constrForm t) == h)
            let
              (lit,hd) = unzip b

            if isJust lt && and lit then redReturn a0 else do
            su <- caseMaybe (sequence ts) (return su) $ \ ts -> do
              let (us,bools) = unzip ts
              fmap ((sequenceA_ us $>) . argN) $ do
              let
                phis :: [Term]
                phis = for bools $ \ m ->
                            foldr (iMin . (\(i,b) -> applyUnless b iNeg $ var i)) iO (IntMap.toList m)
              runNamesT [] $ do
                u <- open u
                [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                phis <- mapM open phis
                us   <- mapM (open . ignoreBlocking) us
                lam "i" $ \ i -> do
                  combine l c (u <@> i) $ zip phis (map (\ t -> t <@> i) us)

            if isJust h && and hd then k (fromMaybe __IMPOSSIBLE__ h) su
                      else noRed' su

      sameConHeadBack (isLit a0) (isCon a0) su $ \ h su -> do
            let u = unArg . ignoreBlocking $ su
            Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
            case nameOfHComp cm of
              Just hcompD -> redReturn $ Def hcompD [] `apply`
                                          (ps ++ map argN [phi,u,a0])
              Nothing        -> noRed' su

    compData mtrD        _     0     DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = redReturn $ unArg a0
    compData (Just trD) isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
      let sc = famThing <$> fsc
      let f = unArg . ignoreBlocking
          phi :: Term
          phi = f $ sphi
      let lam_i = Lam defaultArgInfo . Abs "i"
      redReturn $ Def trD [] `apply` (map (fmap lam_i) ps ++ map argN [phi,unArg a0])

    compData mtrD isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
      let getTermLocal = getTerm $ cmdToName cmd ++ " for data types"
      let sc = famThing <$> fsc
      mhcompName <- getName' builtinHComp
      constrForm <- do
        mz <- getTerm' builtinZero
        ms <- getTerm' builtinSuc
        return $ \ t -> fromMaybe t (constructorForm' mz ms t)
      sa0 <- reduceB' a0
      let f = unArg . ignoreBlocking
          phi = f sphi
          a0 = f sa0
          noRed = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced sa0]
      let lam_i = Lam defaultArgInfo . Abs "i"
      case constrForm a0 of
        Con h _ args -> do
          Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
          case nameOfTransp cm of
              Just transpD -> redReturn $ Def transpD [] `apply`
                                          (map (fmap lam_i) ps ++ map argN [phi,a0])
              Nothing        -> noRed
        Def q es | isHIT, Just q == mhcompName, Just [_l0,_c0,psi,u,u0] <- allApplyElims es -> do
           let bC = ignoreBlocking sc
           hcomp <- getTermLocal builtinHComp
           transp <- getTermLocal builtinTrans
           io <- getTermLocal builtinIOne
           iz <- getTermLocal builtinIZero
           redReturn <=< runNamesT [] $ do
             [l,bC,phi,psi,u,u0] <- mapM (open . unArg) [l,bC,ignoreBlocking sphi,psi,u,u0]
             -- hcomp (sc 1) [psi |-> transp sc phi u] (transp sc phi u0)
             pure hcomp <#> (l <@> pure io) <#> (bC <@> pure io) <#> psi
                   <@> lam "j" (\ j -> ilam "o" $ \ o ->
                        pure transp <#> l <@> bC <@> phi <@> (u <@> j <..> o))
                   <@> (pure transp <#> l <@> bC <@> phi <@> u0)
        _ -> noRed
    compData mtrX isHITorIx nargs cmd l t sbA sphi u u0 = do
      () <- reportSDoc "impossible" 10 $ "compData" <+> (nest 2 . vcat)
       [ "mtrX:       " <+> pretty mtrX
       , "isHITorIx:  " <+> pretty isHITorIx
       , "nargs:      " <+> pretty nargs
       , "cmd:        " <+> text (show cmd)
       , "l:          " <+> familyOrNot l
       , "t:          " <+> familyOrNot t <+> pretty (famThing t)
       , "sbA:          " <+> familyOrNot (ignoreBlocking $ sbA)
       , "sphi:       " <+> pretty (ignoreBlocking sphi)
       , "isJust u:   " <+> pretty (isJust u)
       , "u0:         " <+> pretty u0
       ]
      __IMPOSSIBLE__

--    compData _ _ _ _ _ _ _ _ _ _ = __IMPOSSIBLE__


primComp :: TCM PrimitiveImpl
primComp = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (primIntervalType --> el (cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" primIntervalType $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          nPi' "i" primIntervalType (\ i -> pPi' "o" phi $ \ _ -> el' (a <@> i) (bA <@> i)) -->
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
            redReturn <=< runNamesT [] $ do
              comp <- do
                let imax i j = pure tIMax <@> i <@> j
                    forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                                    <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                                    <@> r
                                                    <@> u
                return $ \ la bA phi u u0 ->
                  pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                              <@> lam "i" (\ i -> ilam "o" $ \ o ->
                                      forward la bA i (u <@> i <..> o))
                              <@> forward la bA (pure iz) u0

              [l,c,phi,u,a0] <- mapM (open . unArg) [l,c,phi,u,a0]
              comp l c phi u a0

      _ -> __IMPOSSIBLE__


prim_glueU' :: TCM PrimitiveImpl
prim_glueU' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (nPi' "i" primIntervalType $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (el's (cl primLevelSuc <@> la) $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       pPi' "o" φ (\ o -> el' la (t <@> cl primIOne <..> o))
         --> (el' la bA)
         --> el' la (cl primHComp <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <@> t <@> bA))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ts ->
    case ts of
      [la,phi,bT,bA,t,a] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA,t,a])
      _ -> __IMPOSSIBLE__

prim_unglueU' :: TCM PrimitiveImpl
prim_unglueU' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (nPi' "i" primIntervalType $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (el's (cl primLevelSuc <@> la) $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       el' la (cl primHComp <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <@> t <@> bA)
         --> el' la bA)
  view <- intervalView'
  one <- primItIsOne
  mglueU <- getPrimitiveName' builtin_glueU
  mtransp <- getPrimitiveName' builtinTrans
  mHCompU <- getPrimitiveName' builtinHComp
  let mhcomp = mHCompU
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ts ->
    case ts of
      [la,phi,bT,bA,b] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> do
           tTransp <- getTerm builtin_unglueU builtinTrans
           iNeg    <- getTerm builtin_unglueU builtinINeg
           iZ      <- getTerm builtin_unglueU builtinIZero
           redReturn <=< runNamesT [] $ do
             [la,bT,b] <- mapM (open . unArg) [la,bT,b]
             pure tTransp <#> lam "i" (\ _ -> la)
                          <@> lam "i" (\ i -> bT <@> (pure iNeg <@> i) <..> pure one)
                          <@> pure iZ
                          <@> b
         _    -> do
            sb <- reduceB' b
            let fallback sbA = return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA] ++ [reduced sb])
            case unArg $ ignoreBlocking $ sb of
               Def q [Apply _,Apply _,Apply _,Apply _,Apply _,Apply a]
                     | Just q == mglueU -> redReturn $ unArg a
               Def q [Apply l,Apply bA,Apply r,Apply u0]
                     | Just q == mtransp -> do
                     sbA <- reduceB bA
                     case unArg $ ignoreBlocking sbA of
                       Lam _ t -> do
                         st <- reduceB' (absBody t)
                         case ignoreBlocking st of
                           Def h es | Just [la,_,phi,bT,bA] <- allApplyElims es, Just h == mHCompU -> do
                             redReturn . fromMaybe __IMPOSSIBLE__ =<< compHCompU DoTransp r Nothing u0 (IsFam (la,phi,bT,bA)) Eliminated
                           _ -> fallback (st *> sbA)
                       _  -> fallback sbA
               Def q [Apply l,Apply bA,Apply r,Apply u,Apply u0]
                     | Just q == mhcomp -> do
                     sbA <- reduceB bA
                     case unArg $ ignoreBlocking sbA of
                       Def h es | Just [la,_,phi,bT,bA] <- allApplyElims es, Just h == mHCompU -> do
                         redReturn . fromMaybe __IMPOSSIBLE__ =<< compHCompU DoHComp r (Just u) u0 (IsNot (la,phi,bT,bA)) Eliminated
                       _ -> fallback sbA
               _ -> return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA] ++ [reduced sb])
      _ -> __IMPOSSIBLE__


primGlue' :: TCM PrimitiveImpl
primGlue' = do
  requireCubical CFull ""
  -- Glue' : ∀ {l} (A : Set l) → ∀ φ → (T : Partial (Set a) φ) (f : (PartialP φ \ o → (T o) -> A))
  --            ([f] : PartialP φ \ o → isEquiv (T o) A (f o)) → Set l
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       nPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       nPi' "T" (pPi' "o" φ $ \ o -> el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       pPi' "o" φ (\ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a)
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
  requireCubical CFull ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       pPi' "o" φ (\ o -> el' lb (t <@> o)) --> (el' la a --> el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)))
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
  requireCubical CFull ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       (el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)) --> el' la a)
  view <- intervalView'
  one <- primItIsOne
  mGlue <- getPrimitiveName' builtinGlue
  mglue <- getPrimitiveName' builtin_glue
  mtransp <- getPrimitiveName' builtinTrans
  mhcomp <- getPrimitiveName' builtinHComp
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
            let fallback sbA = return (NoReduction $ map notReduced [la,lb] ++ map reduced [sbA, sphi] ++ map notReduced [bT,e] ++ [reduced sb])
            case unArg $ ignoreBlocking $ sb of
               Def q [Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply _,Apply a]
                     | Just q == mglue -> redReturn $ unArg a
               Def q [Apply l,Apply bA,Apply r,Apply u0]
                     | Just q == mtransp -> do
                 sbA <- reduceB' bA
                 case unArg $ ignoreBlocking sbA of
                   Lam _ t -> do
                     st <- reduceB' (absBody t)
                     case ignoreBlocking st of
                       Def g es | Just [la',lb',bA',phi',bT',e'] <- allApplyElims es, Just g == mGlue -> do
                           redReturn . fromMaybe __IMPOSSIBLE__ =<< compGlue DoTransp r Nothing u0 (IsFam (la',lb',bA',phi',bT',e')) Eliminated
                       _ -> fallback (st *> sbA)
                   _ -> fallback sbA
               Def q [Apply l,Apply bA,Apply r,Apply u,Apply u0]
                     | Just q == mhcomp -> do
                 sbA <- reduceB' bA
                 case unArg $ ignoreBlocking sbA of
                   Def g es | Just [la',lb',bA',phi',bT',e'] <- allApplyElims es, Just g == mGlue -> do
                       redReturn . fromMaybe __IMPOSSIBLE__ =<< compGlue DoHComp r (Just u) u0 (IsNot (la',lb',bA',phi',bT',e')) Eliminated
                   _ -> fallback sbA
               _ -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e] ++ [reduced sb])
      _ -> __IMPOSSIBLE__


-- TODO Andrea: keep reductions that happen under foralls?
primFaceForall' :: TCM PrimitiveImpl
primFaceForall' = do
  requireCubical CErased ""
  t <- (primIntervalType --> primIntervalType) --> primIntervalType
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \ts -> case ts of
    [phi] -> do
      sphi <- reduceB' phi
      case unArg $ ignoreBlocking $ sphi of
        Lam _ t -> do
          t <- reduce' t
          case t of
            NoAbs _ t -> redReturn t
            Abs _ t ->
              maybe (return $ NoReduction [reduced sphi]) redReturn
                =<< toFaceMapsPrim t
        _ -> return (NoReduction [reduced sphi])
    _ -> __IMPOSSIBLE__
  where
    toFaceMapsPrim t = do
      view <- intervalView'
      unview <- intervalUnview'
      us' <- decomposeInterval t
      fr <- getTerm builtinFaceForall builtinFaceForall
      let v = view t
          us =
            [ map Left (IntMap.toList bsm) ++ map Right ts
              | (bsm, ts) <- us',
                0 `IntMap.notMember` bsm
            ]
          fm (i, b) = if b then var (i - 1) else unview (INeg (argN (var $ i - 1)))
          ffr t = fr `apply` [argN $ Lam defaultArgInfo $ Abs "i" t]
          r =
            Just $
              foldr
                ( (\x r -> unview (IMax (argN x) (argN r)))
                    . foldr
                      (\x r -> unview (IMin (argN (either fm ffr x)) (argN r)))
                      (unview IOne)
                )
                (unview IZero)
                us
      --   traceSLn "cube.forall" 20 (unlines [show v, show us', show us, show r]) $
      return $ case us' of
        [(m, [_])] | null m -> Nothing
        v -> r

decomposeInterval :: HasBuiltins m => Term -> m [(IntMap Bool, [Term])]
decomposeInterval t = do
  decomposeInterval' t <&> \ xs ->
    [ (bm, ts)
    | (bsm :: IntMap BoolSet, ts) <- xs
    , bm <- maybeToList $ traverse BoolSet.toSingleton bsm
        -- discard inconsistent mappings
    ]

decomposeInterval' :: HasBuiltins m => Term -> m [(IntMap BoolSet, [Term])]
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
            , let bsm     = IntMap.fromListWith BoolSet.union $ map (second BoolSet.singleton) bs
            ]


-- | Tries to @primTransp@ a whole telescope of arguments, following the rule for Σ types.
--   If a type in the telescope does not support transp, @transpTel@ throws it as an exception.
transpTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[1]
transpTel = transpTel' False


transpTel' :: (PureTCM m, MonadError TCErr m) =>
          Bool -> Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[1]
transpTel' flag delta phi args = transpSysTel' flag delta [] phi args

type LM m a = NamesT (ExceptT (Closure (Abs Type)) m) a
-- transporting with an extra system/partial element
-- or composing when some of the system is known to be constant.
transpSysTel' :: forall m. (PureTCM m, MonadError TCErr m) =>
          Bool
          -> Abs Telescope -- Γ ⊢ i.Δ
          -> [(Term,Abs [Term])] -- [(ψ,i.δ)] with  Γ,ψ ⊢ i.δ : [i : I]. Δ[i]  -- the proof of [ψ] is not in scope.
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ and all i.δ const on φ ∧ ψ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[1]
transpSysTel' flag delta us phi args = do
  reportSDoc "cubical.prim.transpTel" 20 $
      sep [ text "transpSysTel'"
          , (text "delta  =" <+>) $ nest 2 $ addContext ("i" :: String, __DUMMY_DOM__) $ prettyTCM (unAbs delta)
--          , (text "us =" <+>) $ nest 2 $ prettyList $ map prettyTCM us
          , (text "phi    =" <+>) $ nest 2 $ prettyTCM phi
          , (text "args   =" <+>) $ nest 2 $ prettyList $ map prettyTCM args
          ]
  let getTermLocal = getTerm "transpSys"
  tTransp <- lift primTrans
  tComp <- getTermLocal builtinComp
  tPOr <- getTermLocal builtinPOr
  iz <- lift primIZero
  imin <- lift primIMin
  imax <- lift primIMax
  ineg <- lift primINeg
  let
    noTranspError t = do
      reportSDoc "cubical.prim.transpTel" 20 $ nest 2 $ (text "error type =" <+>) $
        addContext ("i" :: String, __DUMMY_DOM__) $ prettyTCM $ unAbs t
      lift . throwError =<< buildClosure t
    bapp :: forall m a. (Applicative m, Subst a) => m (Abs a) -> m (SubstArg a) -> m a
    bapp t u = lazyAbsApp <$> t <*> u
    doGTransp l t us phi a | null us = pure tTransp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <@> phi <@> a
                           | otherwise = pure tComp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <#> face <@> uphi <@> a
      where
        -- [phi -> a; us]
        face = foldr (\ x y -> pure imax <@> x <@> y) (pure iz) (phi : map fst us)
        uphi = lam "i" $ \ i -> ilam "o" $ \ o -> do
          let sys' = (phi , a) : map (mapSnd (`bapp` i)) us
              sys = map (mapSnd $ ilam "o" . const) sys'
          combine (l <@> i) (unEl <$> bapp t i) __IMPOSSIBLE__ sys <..> o
    combine l ty d [] = d
    combine l ty d [(psi,u)] = u
    combine l ty d ((psi,u):xs)
            = pure tPOr <#> l <@> psi <@> (foldr (\ x y -> pure imax <@> x <@> y) (pure iz) (map fst xs))
                        <#> (ilam "o" $ \ _ -> ty) -- the type
                        <@> u <@> (combine l ty d xs)

    gTransp :: Maybe (LM m Term) -> LM m (Abs Type) -> [(LM m Term,LM m (Abs Term))] -> LM m Term -> LM m Term -> LM m Term
    gTransp (Just l) t u phi a
     | flag = do
      t' <- t
      us' <- mapM snd u
      case ( 0 `freeIn` (raise 1 t' `lazyAbsApp` var 0)
           , 0 `freeIn` map (\ u -> raise 1 u `lazyAbsApp` var 0) us'
           ) of
        (False,False) -> a
        (False,True)  -> doGTransp l t u phi a -- TODO? optimize to "hcomp (l <@> io) (bapp t io) ((phi,NoAbs a):u) a" ?
        (True,_) -> doGTransp l t u phi a
     | otherwise = doGTransp l t u phi a

    gTransp Nothing t sys phi a = do
      let (psis,us) = unzip sys
      -- Γ ⊢ i.Ξ
      xi <- (open =<<) $ do
        bind "i" $ \ i -> do
          TelV xi _ <- (lift . telView =<<) $ t `bapp` i
          return xi
      argnames <- do
        teleArgNames . unAbs <$> xi
      glamN argnames $ \ xi_args -> do
        b' <- bind "i" $ \ i -> do
          ti <- t `bapp` i
          xin <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          xi_args <- xi_args
          ni <- pure ineg <@> i
          phi <- phi
          lift $ piApplyM ti =<< trFillTel' flag xin phi xi_args ni
        usxi <- forM us $ \ u -> bind "i" $ \ i -> do
          ui <- u `bapp` i
          xin <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          xi_args <- xi_args
          ni <- pure ineg <@> i
          phi <- phi
          lift $ apply ui <$> trFillTel' flag xin phi xi_args ni
        axi <- do
          a <- a
          xif <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          phi <- phi
          xi_args <- xi_args
          lift $ apply a <$> transpTel' flag xif phi xi_args
        s <- reduce $ getSort (absBody b')
        reportSDoc "cubical.transp" 20 $ pretty (raise 1 b' `lazyAbsApp` var 0)
        let noTranspSort = if 0 `freeIn` (raise 1 b' `lazyAbsApp` var 0) || 0 `freeIn` (map (`lazyAbsApp` var 0) (raise 1 usxi))
              then noTranspError b'
              else return axi

        case s of
          Type l -> do
            l <- open $ lam_i (Level l)
            b' <- open b'
            axi <- open axi
            usxi <- mapM open usxi
            gTransp (Just l) b' (zip psis usxi) phi axi
          Inf _ n  -> noTranspSort
          SSet _  -> noTranspSort
          SizeUniv -> noTranspSort
          LockUniv -> noTranspSort
          IntervalUniv -> noTranspSort
          Prop{}  -> noTranspSort
          _ -> noTranspError b'
    lam_i = Lam defaultArgInfo . Abs "i"
    go :: Telescope -> [[(Term,Term)]] -> Term -> Args -> ExceptT (Closure (Abs Type)) m Args
    go EmptyTel            [] _  []       = return []
    go (ExtendTel t delta) (u:us) phi (a:args) = do
      -- Γ,i ⊢ t
      -- Γ,i ⊢ (x : t). delta
      -- Γ ⊢ a : t[0]
      s <- reduce $ getSort t
      -- Γ ⊢ b : t[1]    Γ, i ⊢ bf : t[i]
      (b,bf) <- runNamesT [] $ do
        l <- case s of
               SSet _ -> return Nothing
               IntervalUniv -> return Nothing
               SizeUniv     -> return Nothing
               LockUniv     -> return Nothing
               Inf _ n -> return Nothing
               Type l -> Just <$> open (lam_i (Level l))
               _ -> noTranspError (Abs "i" (unDom t))
        t <- open $ Abs "i" (unDom t)
        u <- forM u $ \ (psi,upsi) -> do
              (,) <$> open psi <*> open (Abs "i" upsi)
        [phi,a] <- mapM open [phi, unArg a]
        b <- gTransp l t u phi a
        bf <- bind "i" $ \ i -> do
                            gTransp ((<$> l) $ \ l -> lam "j" $ \ j -> l <@> (pure imin <@> i <@> j))
                                    (bind "j" $ \ j -> t `bapp` (pure imin <@> i <@> j))
                                    u
                                    (pure imax <@> (pure ineg <@> i) <@> phi)
                                    a
        return (b, absBody bf)
      (:) (b <$ a) <$> go (lazyAbsApp delta bf) us phi args
    go EmptyTel            _ _ _ = __IMPOSSIBLE__
    go (ExtendTel t delta) _ _ _ = __IMPOSSIBLE__
  let (psis,uss) = unzip us
      us' | null us = replicate (length args) []
          | otherwise = map (zip psis) $ List.transpose (map absBody uss)
  go (absBody delta) us' phi args

-- | Like @transpTel@ but performing a transpFill.
trFillTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[r]
trFillTel = trFillTel' False

trFillTel' :: (PureTCM m, MonadError TCErr m) =>
          Bool
          -> Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[r]
trFillTel' flag delta phi args r = do
  imin <- lift primIMin
  imax <- lift primIMax
  ineg <- lift primINeg
  transpTel' flag (Abs "j" $ raise 1 delta `lazyAbsApp` (imin `apply` (map argN [var 0, raise 1 r])))
            (imax `apply` [argN $ ineg `apply` [argN r], argN phi])
            args



-- hcompTel' :: Bool -> Telescope -> [(Term,Abs [Term])] -> [Term] -> ExceptT (Closure (Abs Type)) TCM [Term]
-- hcompTel' b delta sides base = undefined

-- hFillTel' :: Bool -> Telescope -- Γ ⊢ Δ
--           -> [(Term,Abs [Term])]  -- [(φ,i.δ)] with  Γ,φ ⊢ i.δ : I → Δ
--           -> [Term]            -- Γ ⊢ δ0 : Δ, matching the [(φ,i.δ)]
--           -> Term -- Γ ⊢ r : I
--           -> ExceptT (Closure (Abs Type)) TCM [Term]
-- hFillTel' b delta sides base = undefined

pathTelescope
  :: forall m. (PureTCM m, MonadError TCErr m) =>
  Telescope -- Δ
  -> [Arg Term] -- lhs : Δ
  -> [Arg Term] -- rhs : Δ
  -> m Telescope
pathTelescope tel lhs rhs = do
  x <- runExceptT (pathTelescope' tel lhs rhs)
  case x of
    Left t -> do
      enterClosure t $ \ t ->
                 typeError . GenericDocError =<<
                    (text "The sort of" <+> pretty t <+> text "should be of the form \"Set l\"")
    Right tel -> return tel

pathTelescope'
  :: forall m. (PureTCM m, MonadError (Closure Type) m) =>
  Telescope -- Δ
  -> [Arg Term] -- lhs : Δ
  -> [Arg Term] -- rhs : Δ
  -> m Telescope
pathTelescope' tel lhs rhs = do
  pathp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPathP
  go pathp (raise 1 tel) lhs rhs
 where
  -- Γ,i ⊢ Δ, Γ ⊢ lhs : Δ[0], Γ ⊢ rhs : Δ[1]
  go :: Term -> Telescope -> [Arg Term] -> [Arg Term] -> m Telescope
  go pathp (ExtendTel a tel) (u : lhs) (v : rhs) = do
    let t = unDom a
    l <- subst 0 __DUMMY_TERM__ <$> getLevel t
    let a' = El (Type l) (apply pathp $ [argH $ Level l] ++ map argN [Lam defaultArgInfo (Abs "i" $ unEl t), unArg u, unArg v])
        -- Γ,eq : u ≡ v, i : I ⊢ m = eq i : t[i]
        -- m  = runNames [] $ do
        --        [u,v] <- mapM (open . unArg) [u,v]
        --        bind "eq" $ \ eq -> bind "i" $ \ i ->
    (ExtendTel (a' <$ a) <$>) . runNamesT [] $ do
      let nm = (absName tel)
      tel <- open $ Abs "i" tel
      [u,v] <- mapM (open . unArg) [u,v]
      [lhs,rhs] <- mapM open [lhs,rhs]
      bind nm $ \ eq -> do
        lhs <- lhs
        rhs <- rhs
        tel' <- bind "i" $ \ i ->
                  lazyAbsApp <$> (lazyAbsApp <$> tel <*> i) <*> (eq <@@> (u, v, i))
        lift $ go pathp (absBody tel') lhs rhs
  go _ EmptyTel [] [] = return EmptyTel
  go _ _ _ _ = __IMPOSSIBLE__
  getLevel :: Type -> m Level
  getLevel t = do
    s <- reduce $ getSort t
    case s of
      Type l -> pure l
      s      -> throwError =<< buildClosure t

combineSys :: HasBuiltins m => NamesT m Term -> NamesT m Term -> [(NamesT m Term, NamesT m Term)] -> NamesT m Term
combineSys l ty xs = snd <$> combineSys' l ty xs

combineSys' :: HasBuiltins m => NamesT m Term -> NamesT m Term -> [(NamesT m Term, NamesT m Term)] -> NamesT m (Term,Term)
combineSys' l ty xs = do
    tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
    tMax <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMax
    iz <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIZero
    tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIsOneEmpty

    let
      max i j = pure tMax <@> i <@> j
      pOr l ty phi psi u0 u1 = do
          pure tPOr <#> l
                    <@> phi <@> psi
                    <#> (ilam "o" $ \ _ -> ty) <@> u0 <@> u1

      -- TODO: optimize the foldr away?
      combine [] = pure tEmpty <#> l <#> (ilam "o" $ \ _ -> ty)
      combine [(psi,u)] = u
      combine ((psi,u):xs) = pOr l ty psi (foldr max (pure iz) (map fst xs)) u (combine xs)
    (,) <$> foldr max (pure iz) (map fst xs) <*> combine xs


data TranspError = CannotTransp {errorType :: (Closure (Abs Type)) }

instance Exception TranspError
instance Show TranspError where
  show _ = "TranspError"

tryTranspError :: TCM a -> TCM (Either (Closure (Abs Type)) a)
tryTranspError (TCM m) = TCM $ \ s env -> do
  mapLeft errorType <$> (try (m s env))

transpPathPTel' ::
             NamesT TCM (Abs (Abs Telescope)) -- ^ j.i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[0,i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[1,i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : PathP (λ j → Δ[j,0]) (x 0) (y 0)
             -> NamesT TCM [Arg Term] -- PathP (λ j → Δ[j,0]) (x 1) (y 1) [ φ ↦ q ]
transpPathPTel' theTel x y phi p = do
 let neg j = cl primINeg <@> j
 -- is the open overkill?
 qs <- (open =<<) $ fmap (fmap (\ (Abs n (Arg i t)) -> Arg i (Lam defaultArgInfo $ Abs n t)) . sequenceA)
                  $ bind "j" $ \ j -> do
   theTel <- absApp <$> theTel <*> j
   faces <- sequence [neg j, j]
   us <- forM [x,y] $ \ z -> do
           bind "i" $ \ i -> forM z (<@> i)
   let sys = zip faces us
   -- [(neg j, bind "i" $ \ i -> flip map x (<@> i))
   -- ,(j , bind "i" $ \ i -> flip map y (<@> i))]
   phi <- phi
   p0 <- mapM (<@> j) p
   let toArgs = zipWith (\ a t -> t <$ a) (teleArgNames (unAbs $ theTel))
   eq <- lift . runExceptT $ transpSysTel' False theTel sys phi (toArgs p0)
   either (lift . lift . throw . CannotTransp) pure eq
 qs

transpPathTel' ::
             NamesT TCM (Abs Telescope) -- ^ i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (Δ[0]) (x 0) (y 0)
             -> NamesT TCM [Arg Term] -- Path (Δ[1]) (x 1) (y 1) [ φ ↦ q ]
transpPathTel' theTel x y phi p = do
 let neg j = cl primINeg <@> j
 -- is the open overkill?
 qs <- (open =<<) $ fmap (fmap (\ (Abs n (Arg i t)) -> Arg i (Lam defaultArgInfo $ Abs n t)) . sequenceA)
                  $ bind "j" $ \ j -> do
   theTel <- theTel
   faces <- sequence $ [neg j, j]
   us <- forM [x,y] $ \ z -> do
           bind "i" $ \ i -> forM z (<@> i)
   let sys = zip faces us
   -- [(neg j, bind "i" $ \ i -> flip map x (<@> i))
   -- ,(j , bind "i" $ \ i -> flip map y (<@> i))]
   phi <- phi
   p0 <- mapM (<@> j) p
   let toArgs = zipWith (\ a t -> t <$ a) (teleArgNames (unAbs theTel))
   eq <- lift . runExceptT $ transpSysTel' False theTel sys phi (toArgs p0)
   either (lift . lift . throw . CannotTransp) pure eq
 qs

trFillPathTel' ::
               NamesT TCM (Abs Telescope) -- ^ i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (Δ[0]) (x 0) (y 0)
             -> NamesT TCM Term            -- ^ r
             -> NamesT TCM [Arg Term] -- Path (Δ[r]) (x r) (y r) [ φ ↦ q; (r = 0) ↦ q ]
trFillPathTel' tel x y phi p r = do
  let max i j = cl primIMin <@> i <@> j
  let min i j = cl primIMin <@> i <@> j
  let neg i = cl primINeg <@> i
  x' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM x (<@> (min r i))
  y' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM y (<@> (min r i))
  transpPathTel' (bind "i" $ \ i -> absApp <$> tel <*> min r i)
                 x'
                 y'
                 (max phi (neg r))
                 p

trFillPathPTel' ::
               NamesT TCM (Abs (Abs Telescope)) -- ^ j.i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[0,i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[1,i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (\ j -> Δ[j,0]) (x 0) (y 0)
             -> NamesT TCM Term            -- ^ r
             -> NamesT TCM [Arg Term] -- Path (\ j → Δ[j,r]) (x r) (y r) [ φ ↦ q; (r = 0) ↦ q ]
trFillPathPTel' tel x y phi p r = do
  let max i j = cl primIMin <@> i <@> j
  let min i j = cl primIMin <@> i <@> j
  let neg i = cl primINeg <@> i
  x' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM x (<@> (min r i))
  y' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM y (<@> (min r i))
  transpPathPTel' (bind "j" $ \ j -> bind "i" $ \ i -> absApp <$> (absApp <$> tel <*> j) <*> min r i)
                 x'
                 y'
                 (max phi (neg r))
                 p



-- given Γ ⊢ I type, and Γ ⊢ Δ telescope, build Δ^I such that
-- Γ ⊢ (x : A, y : B x, ...)^I = (x : I → A, y : (i : I) → B (x i), ...)
expTelescope :: Type -> Telescope -> Telescope
expTelescope int tel = unflattenTel names ys
  where
    stel = size tel
    xs = flattenTel tel
    names = teleNames tel
    t = ExtendTel (defaultDom $ raise stel int) (Abs "i" EmptyTel)
    s = expS stel
    ys = map (fmap (abstract t) . applySubst s) xs


-- | Γ, Δ^I, i : I |- expS |Δ| : Γ, Δ
expS :: Nat -> Substitution
expS stel = prependS __IMPOSSIBLE__
  [ Just (var n `apply` [Arg defaultArgInfo $ var 0]) | n <- [1..stel] ]
  (raiseS (stel + 1))


-- * Special cases of Type
-----------------------------------------------------------

-- | A @Type@ with sort @Type l@.
--   Such a type supports both hcomp and transp.
data LType = LEl Level Term deriving (Eq,Show)

fromLType :: LType -> Type
fromLType (LEl l t) = El (Type l) t

lTypeLevel :: LType -> Level
lTypeLevel (LEl l t) = l

toLType :: MonadReduce m => Type -> m (Maybe LType)
toLType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LEl l (unEl ty)
    _      -> return $ Nothing

instance Subst LType where
  type SubstArg LType = Term
  applySubst rho (LEl l t) = LEl (applySubst rho l) (applySubst rho t)

-- | A @Type@ that either has sort @Type l@ or is a closed definition.
--   Such a type supports some version of transp.
--   In particular we want to allow the Interval as a @ClosedType@.
data CType = ClosedType Sort QName | LType LType deriving (Eq,Show)

instance P.Pretty CType where
  pretty = P.pretty . fromCType

fromCType :: CType -> Type
fromCType (ClosedType s q) = El s (Def q [])
fromCType (LType t) = fromLType t

toCType :: MonadReduce m => Type -> m (Maybe CType)
toCType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LType (LEl l (unEl ty))
    SSet{} -> do
      t <- reduce (unEl ty)
      case t of
        Def q [] -> return $ Just $ ClosedType sort q
        _        -> return $ Nothing
    _      -> return $ Nothing

instance Subst CType where
  type SubstArg CType = Term
  applySubst rho (ClosedType s q) = ClosedType (applySubst rho s) q
  applySubst rho (LType t) = LType $ applySubst rho t

hcomp :: (HasBuiltins m, MonadError TCErr m, MonadReduce m) =>
               NamesT m Type
               -> [(NamesT m Term, NamesT m Term)]
               -> NamesT m Term
               -> NamesT m Term
hcomp ty sys u0 = do
  iz <- primIZero
  tHComp <- primHComp
  let max i j = cl primIMax <@> i <@> j
  ty <- ty
  Just (LEl l ty) <- toLType ty
  l <- open $ Level l
  ty <- open $ ty
  face <- (foldr max (pure iz) $ map fst $ sys)
  sys <- lam "i'" $ \ i -> combineSys l ty [(phi, u <@> i) | (phi,u) <- sys]
  pure tHComp <#> l <#> ty <#> pure face <@> pure sys <@> u0

transpSys :: (HasBuiltins m, MonadError TCErr m, MonadReduce m) =>
               NamesT m (Abs Type) -- ty
               -> [(NamesT m Term, NamesT m Term)] -- sys
               -> NamesT m Term -- φ
               -> NamesT m Term
               -> NamesT m Term
transpSys ty sys phi u = do
  let max i j = cl primIMax <@> i <@> j
  iz <- primIZero
  tTransp <- primTrans
  tComp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinComp
  l_ty <- bind "i" $ \ i -> do
      ty <- absApp <$> ty <*> i
      Just (LEl l ty) <- toLType ty
      return (l,ty)
  l <- open $ Lam defaultArgInfo . fmap (Level . fst) $ l_ty
  ty <- open $ Lam defaultArgInfo . fmap snd $ l_ty

  if null sys then pure tTransp <#> l <@> ty <@> phi <@> u else do

  let face = max phi (foldr max (pure iz) $ map fst $ sys)
  sys <- (open =<<) $ lam "i'" $ \ i -> do
    let base = (phi, ilam "o" $ \ _ -> u)
    combineSys l ty $ base : [(phi, u <@> i) | (phi,u) <- sys]

  pure tComp <#> l <@> ty <#> face <@> sys <@> u

debugClause :: String -> Clause -> TCM ()
debugClause s c = do
      reportSDoc s 20 $
        "gamma:" <+> prettyTCM gamma
      reportSDoc s 20 $ addContext gamma $
        "ps   :" <+> prettyTCM (patternsToElims ps)
      reportSDoc s 20 $ addContext gamma $
        "type :" <+> maybe "nothing" prettyTCM rhsTy
      reportSDoc s 20 $ addContext gamma $
        "body :" <+> maybe "nothing" prettyTCM rhs

      reportSDoc s 30 $
        addContext gamma $ "c:" <+> pretty c
  where
    gamma = clauseTel c
    ps = namedClausePats c
    rhsTy = clauseType c
    rhs = clauseBody c
