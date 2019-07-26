{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Primitive.Cubical where

import Prelude hiding (null, (!!))

import Control.Monad
import Control.Monad.Trans ( lift )

import Data.Either ( partitionEithers )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optCubical )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple

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
primIMin' = do
  requireCubical
  primIBin IOne IZero

primIMax' :: TCM PrimitiveImpl
primIMax' = do
  requireCubical
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
                       <#> phi
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

data FamilyOrNot a
  = IsFam { famThing :: a }
  | IsNot { famThing :: a }
  deriving (Eq,Show,Functor,Foldable,Traversable)

instance Reduce a => Reduce (FamilyOrNot a) where
  reduceB' x = traverse id <$> traverse reduceB' x
  reduce' x = traverse reduce' x


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
      imin i j = pure tIMin <@> i <@> j
  let forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                      <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                      <@> r
                                      <@> u
  return $ \ la bA phi u u0 ->
    pure tHComp <#> (la <@> pure io)
                <#> (bA <@> pure io)
                <#> imax phi (ineg phi)
                <@> (lam "i" $ \ i ->
                      pure tPOr <#> (la <@> i)
                                <@> phi
                                <@> ineg phi
                                <@> (ilam "o" $ \ a -> bA <@> i)
                                <@> (ilam "o" $ \ o -> forward la bA i (u <@> i <..> o))
                                <@> (ilam "o" $ \ o -> forward la bA (pure iz) u0))
                <@> forward la bA (pure iz) u0


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
               mHComp <- getPrimitiveName' builtinHComp
               mGlue <- getPrimitiveName' builtinGlue
               mId   <- getBuiltinName' builtinId
               pathV <- pathView'
               case famThing t of
                 MetaV m _ -> fallback' (fmap famThing $ Blocked m () *> sbA)
                 -- absName t instead of "i"
                 Pi a b | nelims > 0  -> maybe fallback redReturn =<< compPi cmd "i" ((a,b) <$ t) (ignoreBlocking sphi) u u0
                        | otherwise -> fallback

                 Sort (Type l) | DoTransp <- cmd -> compSort cmd fallback phi u u0 (l <$ t)

                 Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
                   compGlue cmd phi u u0 ((la, lb, bA, phi', bT, e) <$ t)

                 Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
                   | Just q == mHComp, Sort (Type la) <- unArg s  -> do
                   compHCompU cmd phi u u0 ((Level la <$ s, phi', bT, bA) <$ t)

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

                         | Just as <- allApplyElims es, [] <- recFields r -> compData False (recPars r) cmd l (as <$ t) sbA sphi u u0
                     Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons}
                       | and [null pcons | DoHComp  <- [cmd]], Just as <- allApplyElims es -> compData (not $ null $ pcons) (pars+ixs) cmd l (as <$ t) sbA sphi u u0
                     -- postulates with no arguments do not need to transport.
                     Axiom{} | [] <- es, DoTransp <- cmd -> redReturn $ unArg u0
                     _          -> fallback

                 _ -> fallback
  where
    compSort DoTransp fallback phi Nothing u0 (IsFam l) = do
      -- TODO should check l is constant
      redReturn $ unArg u0
    -- compSort DoHComp fallback phi (Just u) u0 (IsNot l) = -- hcomp for Set is a whnf, handled above.
    compSort _ fallback phi u u0 _ = __IMPOSSIBLE__
    compHCompU DoHComp psi (Just u) u0 (IsNot (la, phi, bT, bA)) = do
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
      (redReturn =<<) . runNamesT [] $ do
        [psi, u, u0] <- mapM (open . unArg) [psi, u, u0]
        [la, phi, bT, bA] <- mapM (open . unArg) [la, phi, bT, bA]
        let
          hfill la bA phi u u0 i = pure tHComp <#> la
                                               <#> bA
                                               <#> (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               <@> (lam "j" $ \ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <@> (ilam "o" $ \ a -> bA)
                                                     <@> (ilam "o" $ \ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> (ilam "o" $ \ _ -> u0)
                                                   )
                                               <@> u0
          transp la bA a0 = pure tTransp <#> (lam "i" $ const la) <@> lam "i" bA <@> pure iz <@> a0
          tf i o = hfill la (bT <@> pure io <..> o) psi u u0 i
          bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
          unglue g = pure tunglue <#> la <#> phi <#> bT <#> bAS <@> g
          a1 = pure tHComp <#> la <#> bA <#> (pure tIMax <@> psi <@> phi)
                           <@> (lam "i" $ \ i -> pure tPOr <#> la <@> psi <@> phi <@> (ilam "_" $ \ _ -> bA)
                                 <@> (ilam "o" $ \ o -> unglue (u <@> i <..> o))
                                 <@> (ilam "o" $ \ o -> transp la (\ i -> bT <@> (pure tINeg <@> i) <..> o) (tf i o))
                               )
                           <@> unglue u0
          t1 = tf (pure io)
        pure tglue <#> la <#> phi <#> bT <#> bAS <@> (ilam "o" $ \ o -> t1 o) <@> a1
    compHCompU DoTransp psi Nothing u0 (IsFam (la, phi, bT, bA)) = do
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
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      (redReturn =<<) . runNamesT [] $ do
        let ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            imin i j = pure tIMin <@> i <@> j
            transp la bA a0 = pure tTrans <#> (lam "i" $ const la) <@> lam "i" bA <@> pure iz <@> a0

        gcomp <- mkGComp localUse

        let transpFill la bA phi u0 i =
              pure tTrans <#> (ilam "j" $ \ j -> la <@> imin i j)
                          <@> (ilam "j" $ \ j -> bA <@> imin i j)
                          <@> (imax phi (ineg i))
                          <@> u0
        [psi,u0] <- mapM (open . unArg) [psi,u0]
        glue1 <- do
          tglue   <- cl $ getTermLocal builtin_glueU
          [la, phi, bT, bA] <- mapM (open . unArg . subst 0 io) $ [la, phi, bT, bA]
          let bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
          g <- (open =<<) $ pure tglue <#> la <#> phi <#> bT <#> bAS
          return $ \ t a -> g <@> t <@> a
        unglue0 <- do
          tunglue <- cl $ getTermLocal builtin_unglueU
          [la, phi, bT, bA] <- mapM (open . unArg . subst 0 iz) $ [la, phi, bT, bA]
          let bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
          ug <- (open =<<) $ pure tunglue <#> la <#> phi <#> bT <#> bAS
          return $ \ a -> ug <@> a
        [la, phi, bT, bA] <- mapM (\ a -> open . runNames [] $ (lam "i" $ const (pure $ unArg a))) [la, phi, bT, bA]
        let
          lb = la
          tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <@> pure io <..> o) psi u0 i
          t1 o = tf (pure io) o
          a0 = unglue0 u0

          -- compute "forall. phi"
          forallphi = pure tForall <@> phi

          -- a1 with gcomp
          a1 = gcomp la bA
                 (imax psi forallphi)
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i)
                                             <@> psi
                                             <@> forallphi
                                             <@> (ilam "o" $ \ a -> bA <@> i)
                                             <@> (ilam "o" $ \ _ -> a0)
                                             <@> (ilam "o" $ \ o -> transp (la <@> i)
                                                                           (\ j -> bT <@> i <@> ineg j <..> o)
                                                                           (tf i o)))
                 a0

--          max l l' = pure tLMax <@> l <@> l'
          sigCon x y = pure (Con (sigmaCon kit) ConOSystem []) <@> x <@> y
          w i o = lam "x" $
                  transp (la <@> i)
                         (\ j -> bT <@> i <@> ineg j <..> o)
          fiber la lb bA bB f b =
            (pure (Def (sigmaName kit) []) <#> la
                                           <#> lb
                                           <@> bA
                                           <@> (lam "a" $ \ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b))

          pt o = -- o : [ φ 1 ]
            pure tPOr <#> (la <@> pure io)
                      <@> psi
                      <@> forallphi
                      <@> (ilam "o" $ \ _ -> bT <@> pure io <@> pure io <..> o)
                      <@> (ilam "o" $ \ o -> u0)
                      <@> (ilam "o" $ \ o -> t1 o)

          -- "ghcomp" is implemented in the proof of tTranspProof
          -- (see src/data/lib/prim/Agda/Builtin/Cubical/HCompU.agda)
          t1'alpha o = -- o : [ φ 1 ]
             pure tTranspProof <#> (la <@> pure io)
                               <@> (lam "i" $ \ i -> bT <@> pure io <@> ineg i <..> o)
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
                  <@> (lam "j" $ \ j ->
                         pure tPOr <#> (la <@> pure io) <@> (phi <@> pure io) <@> psi <@> (ilam "o" $ \ _ -> bA <@> pure io)
                                   <@> (ilam "o" $ \ o -> alpha o <@@> (w (pure io) o <@> t1' o,a1,j))
                                   <@> (ilam "o" $ \ _ -> a1)
                      )
                  <@> a1
        glue1 (ilam "o" t1') a1'
    compHCompU _ psi _ u0 _ = __IMPOSSIBLE__
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
      kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
      (redReturn =<<) . runNamesT [] $ do
        let ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            imin i j = pure tIMin <@> i <@> j

        gcomp <- mkGComp localUse

        let transpFill la bA phi u0 i =
              pure tTrans <#> (ilam "j" $ \ j -> la <@> imin i j)
                          <@> (ilam "j" $ \ j -> bA <@> imin i j)
                          <@> (imax phi (ineg i))
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

          -- compute "forall. phi"
          forallphi = pure tForall <@> phi

          -- a1 with gcomp
          a1 = gcomp la bA
                 (imax psi forallphi)
                 (lam "i" $ \ i -> pure tPOr <#> (la <@> i)
                                             <@> psi
                                             <@> forallphi
                                             <@> (ilam "o" $ \ a -> bA <@> i)
                                             <@> (ilam "o" $ \ _ -> a0)
                                             <@> (ilam "o" $ \ o -> pure tEFun <#> (lb <@> i)
                                                                               <#> (la <@> i)
                                                                               <#> (bT <@> i <..> o)
                                                                               <#> (bA <@> i)
                                                                               <@> (e <@> i <..> o)
                                                                               <@> (tf i o)))
                 a0

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
                                           <@> (lam "a" $ \ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b))

          -- We don't have to do anything special for "~ forall. phi"
          -- here (to implement "ghcomp") as it is taken care off by
          -- tEProof in t1'alpha below
          pe o = -- o : [ φ 1 ]
            pure tPOr <#> max (la <@> pure io) (lb <@> pure io)
                      <@> psi
                      <@> forallphi
                      <@> (ilam "o" $ \ _ ->
                             fiber (lb <@> pure io) (la <@> pure io)
                                   (bT <@> (pure io) <..> o) (bA <@> pure io)
                                   (w (pure io) o) a1)
                      <@> (ilam "o" $ \ o -> sigCon u0 (lam "_" $ \ _ -> a1))
                      <@> (ilam "o" $ \ o -> sigCon (t1 o) (lam "_" $ \ _ -> a1))

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
              IsFam (a,_) -> (a, \ a -> runNames [] $ (lam "i" $ const (pure a)))
              IsNot (a,_) -> (a, id)
        lx <- toLevel' x
        caseMaybe lx (return Nothing) $ \ lx -> Just <$>
          mapM (open . f) [Level lx, unEl . unDom $ x]
      caseMaybe labA (return Nothing) $ \ [la,bA] -> Just <$> do
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
            andM . for as $ \ (bs,ts) -> do
                 let u' = listS (Map.toAscList $ Map.map boolToI bs) `applySubst` u
                 t <- reduce2Lam u'
                 return $! p $ ignoreBlocking t
    reduce2Lam t = do
          t <- reduce' t
          case lam2Abs t of
            t -> underAbstraction_ t $ \ t -> do
               t <- reduce' t
               case lam2Abs t of
                 t -> underAbstraction_ t reduceB'
         where
           lam2Abs (Lam _ t) = absBody t <$ t
           lam2Abs t         = Abs "y" (raise 1 t `apply` [argN $ var 0])
    allComponentsBack unview phi u p = do
            let
              boolToI b = if b then unview IOne else unview IZero
              lamlam t = Lam defaultArgInfo (Abs "i" (Lam (setRelevance Irrelevant defaultArgInfo) (Abs "o" t)))
            as <- decomposeInterval phi
            (flags,t_alphas) <- fmap unzip . forM as $ \ (bs,ts) -> do
                 let u' = listS bs' `applySubst` u
                     bs' = (Map.toAscList $ Map.map boolToI bs)
                 let weaken = foldr composeS idS $ map (\ j -> liftS j (raiseS 1)) $ map fst bs'
                 t <- reduce2Lam u'
                 return $ (p $ ignoreBlocking t, listToMaybe [ (weaken `applySubst` (lamlam <$> t),bs) | null ts ])
            return $ (flags,t_alphas)
    compData False _ cmd@DoHComp (IsNot l) (IsNot ps) fsc sphi (Just u) a0 = do
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
          u = f su
          a0 = f sa0
          isLit t@(Lit lt) = Just t
          isLit _ = Nothing
          isCon (Con h _ _) = Just h
          isCon _           = Nothing
          combine l ty d [] = d
          combine l ty d [(psi,u)] = u
          combine l ty d ((psi,u):xs)
            = pure tPOr <#> l <@> psi <@> (foldr imax iz (map fst xs))
                        <#> (ilam "o" $ \ _ -> ty) -- the type
                        <@> u <@> (combine l ty d xs)
          noRed' su = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
            where
              su' = case view phi of
                     IZero -> notBlocked $ argN $ runNames [] $ do
                                 [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                                 lam "i" $ \ i -> pure tEmpty <#> l
                                                              <#> (ilam "o" $ \ _ -> c)
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
                            foldr iMin iO $ map (\(i,b) -> if b then var i else iNeg (var i)) $ Map.toList m
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

    compData _     0 DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = redReturn $ unArg a0
    compData isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
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
           (redReturn =<<) . runNamesT [] $ do
             [l,bC,phi,psi,u,u0] <- mapM (open . unArg) [l,bC,ignoreBlocking sphi,psi,u,u0]
             -- hcomp (sc 1) [psi |-> transp sc phi u] (transp sc phi u0)
             pure hcomp <#> (l <@> pure io) <#> (bC <@> pure io) <#> psi
                   <@> (lam "j" $ \ j -> ilam "o" $ \ o ->
                        pure transp <#> l <@> bC <@> phi <@> (u <@> j <..> o))
                   <@> (pure transp <#> l <@> bC <@> phi <@> u0)
        _ -> noRed
    compData _ _ _ _ _ _ _ _ _ = __IMPOSSIBLE__
    compPO = __IMPOSSIBLE__

primComp :: TCM PrimitiveImpl
primComp = do
  requireCubical
  t    <- runNamesT [] $
          hPi' "a" (elInf (cl primInterval) --> (el $ cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" (elInf (cl primInterval)) $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          hPi' "φ" (elInf $ cl primInterval) $ \ phi ->
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
                  ineg j = (pure tINeg <@> j) :: TCMT IO Term
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


prim_glueU' :: TCM PrimitiveImpl
prim_glueU' = do
  requireCubical
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (nPi' "i" (elInf $ cl primInterval) $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (elInf $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       (pPi' "o" φ $ \ o -> el' la (t <@> cl primIOne <..> o))
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
  requireCubical
  t <- runNamesT [] $
       (hPi' "la" (el $ cl primLevel) $ \ la ->
       hPi' "φ" (elInf $ cl primInterval) $ \ φ ->
       hPi' "T" (nPi' "i" (elInf $ cl primInterval) $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (elInf $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       el' la (cl primHComp <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <@> t <@> bA)
         --> el' la bA)
  view <- intervalView'
  one <- primItIsOne
  mglueU <- getPrimitiveName' builtin_glueU
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ts ->
    case ts of
      [la,phi,bT,bA,b] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> do
           tTransp <- getTerm builtin_unglueU builtinTrans
           iNeg    <- getTerm builtin_unglueU builtinINeg
           iZ      <- getTerm builtin_unglueU builtinIZero
           (redReturn =<<) . runNamesT [] $ do
             [la,bT,b] <- mapM (open . unArg) [la,bT,b]
             pure tTransp <#> (lam "i" $ \ _ -> la)
                          <@> (lam "i" $ \ i -> bT <@> (pure iNeg <@> i) <..> pure one)
                          <@> pure iZ
                          <@> b
         _    -> do
            sb <- reduceB' b
            case unArg $ ignoreBlocking $ sb of
               Def q [Apply _,Apply _,Apply _,Apply _,Apply _,Apply a]
                     | Just q == mglueU -> redReturn $ unArg a
               _ -> return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA] ++ [reduced sb])
      _ -> __IMPOSSIBLE__


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


-- | Tries to @primTransp@ a whole telescope of arguments, following the rule for Σ types.
--   If a type in the telescope does not support transp, @transpTel@ throws it as an exception.
transpTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[1]
transpTel delta phi args = do
  tTransp <- liftTCM primTrans
  imin <- liftTCM primIMin
  imax <- liftTCM primIMax
  ineg <- liftTCM primINeg
  let
    noTranspError t = lift . throwError =<< liftTCM (buildClosure t)
    bapp :: (Applicative m, Subst t a) => m (Abs a) -> m t -> m a
    bapp t u = lazyAbsApp <$> t <*> u
    gTransp (Just l) t phi a = pure tTransp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <@> phi <@> a
    gTransp Nothing  t phi a = do
      -- Γ ⊢ i.Ξ
      xi <- (open =<<) $ do
        bind "i" $ \ i -> do
          TelV xi _ <- (liftTCM . telView =<<) $ t `bapp` i
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
          lift $ piApplyM ti =<< trFillTel xin phi xi_args ni
        axi <- do
          a <- a
          xif <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          phi <- phi
          xi_args <- xi_args
          lift $ apply a <$> transpTel xif phi xi_args
        s <- reduce $ getSort (absBody b')
        case s of
          Type l -> do
            l <- open $ lam_i (Level l)
            b' <- open b'
            axi <- open axi
            gTransp (Just l) b' phi axi
          Inf    ->
            case 0 `freeIn` (raise 1 b' `lazyAbsApp` var 0) of
              False -> return axi
              True -> noTranspError b'
          _ -> noTranspError b'
    lam_i = Lam defaultArgInfo . Abs "i"
    go :: Telescope -> Term -> Args -> ExceptT (Closure (Abs Type)) TCM Args
    go EmptyTel            _   []       = return []
    go (ExtendTel t delta) phi (a:args) = do
      -- Γ,i ⊢ t
      -- Γ,i ⊢ (x : t). delta
      -- Γ ⊢ a : t[0]
      s <- reduce $ getSort t
      -- Γ ⊢ b : t[1], Γ,i ⊢ b : t[i]
      (b,bf) <- runNamesT [] $ do
        l <- case s of
               Inf -> return Nothing
               Type l -> Just <$> open (lam_i (Level l))
               _ -> noTranspError (Abs "i" (unDom t))
        t <- open $ Abs "i" (unDom t)
        [phi,a] <- mapM open [phi, unArg a]
        b <- gTransp l t phi a
        bf <- bind "i" $ \ i -> do
                            gTransp ((<$> l) $ \ l -> lam "j" $ \ j -> l <@> (pure imin <@> i <@> j))
                                    (bind "j" $ \ j -> t `bapp` (pure imin <@> i <@> j))
                                    (pure imax <@> (pure ineg <@> i) <@> phi)
                                    a
        return (b, absBody bf)
      (:) (b <$ a) <$> go (lazyAbsApp delta bf) phi args
    go (ExtendTel t delta) phi []    = __IMPOSSIBLE__
    go EmptyTel            _   (_:_) = __IMPOSSIBLE__
  go (absBody delta) phi args

-- | Like @transpTel@ but performing a transpFill.
trFillTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[r]
trFillTel delta phi args r = do
  imin <- liftTCM primIMin
  imax <- liftTCM primIMax
  ineg <- liftTCM primINeg
  transpTel (Abs "j" $ raise 1 delta `lazyAbsApp` (imin `apply` (map argN [var 0, raise 1 r])))
            (imax `apply` [argN $ ineg `apply` [argN r], argN phi])
            args
