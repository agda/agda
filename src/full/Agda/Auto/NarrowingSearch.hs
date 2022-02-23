
module Agda.Auto.NarrowingSearch where

import Control.Monad       ( foldM, when )
import Control.Monad.State ( MonadState(..), modify, StateT, evalStateT, runStateT )
import Control.Monad.Trans ( lift )

import Data.IORef hiding (writeIORef, modifyIORef)
import qualified Data.IORef as NoUndo (writeIORef, modifyIORef)

import Agda.Utils.Impossible
import Agda.Utils.Empty

newtype Prio = Prio { getPrio :: Int }
 deriving (Eq, Ord, Num)

class Trav a where
  type Block a
  trav :: Monad m => (forall b. TravWith b (Block a) => MM b (Block b) -> m ()) -> a -> m ()

-- | Trav instance 'a' with block type 'blk'
type TravWith a blk = (Trav a, Block a ~ blk)

instance TravWith a blk => Trav (MM a blk) where
  type Block (MM a blk) = blk
  trav f me = f me

data Term blk = forall a. TravWith a blk => Term a

-- | Result of type-checking.
data Prop blk
  = OK
    -- ^ Success.
  | Error String
    -- ^ Definite failure.
  | forall a . AddExtraRef String (Metavar a blk) (Move' blk a)
    -- ^ Experimental.
  | And (Maybe [Term blk]) (MetaEnv (PB blk)) (MetaEnv (PB blk))
    -- ^ Parallel conjunction of constraints.
  | Sidecondition (MetaEnv (PB blk)) (MetaEnv (PB blk))
    -- ^ Experimental, related to 'mcompoint'.
    -- First arg is sidecondition.
  | Or Prio (MetaEnv (PB blk)) (MetaEnv (PB blk))
    -- ^ Forking proof on something that is not part of the term language.
    --   E.g. whether a term will reduce or not.
  | ConnectHandle (OKHandle blk) (MetaEnv (PB blk))
    -- ^ Obsolete.

data OKVal = OKVal
type OKHandle blk = MM OKVal blk
type OKMeta blk = Metavar OKVal blk

-- | Agsy's meta variables.
--
--   @a@ the type of the metavariable (what it can be instantiated with).
--   @blk@ the search control information (e.g. the scope of the meta).

data Metavar a blk = Metavar
  { mbind :: IORef (Maybe a)
    -- ^ Maybe an instantiation (refinement).  It is usually shallow,
    --   i.e., just one construct(or) with arguments again being metas.
  , mprincipalpresent :: IORef Bool
    -- ^ Does this meta block a principal constraint
    --   (i.e., a type-checking constraint).
  , mobs :: IORef [(QPB a blk, Maybe (CTree blk))]
    -- ^ List of observers, i.e., constraints blocked by this meta.
  , mcompoint :: IORef [SubConstraints blk]
    -- ^ Used for experiments with independence of subproofs.
  , mextrarefs :: IORef [Move' blk a]
    -- ^ Experimental.
  }

hequalMetavar :: Metavar a1 blk1 -> Metavar a2 bkl2 -> Bool
hequalMetavar m1 m2 = mprincipalpresent m1 == mprincipalpresent m2

instance Eq (Metavar a blk) where
 x == y = hequalMetavar x y

newMeta :: IORef [SubConstraints blk] -> IO (Metavar a blk)
newMeta mcompoint = do
 bind <- newIORef Nothing
 pp <- newIORef False
 obs <- newIORef []
 erefs <- newIORef []
 return $ Metavar bind pp obs mcompoint erefs

initMeta :: IO (Metavar a blk)
initMeta = do
 cp <- newIORef []
 newMeta cp

data CTree blk = CTree
 {ctpriometa :: IORef (PrioMeta blk),
  ctsub :: IORef (Maybe (SubConstraints blk)),
  ctparent :: IORef (Maybe (CTree blk)), -- Nothing - root
  cthandles :: IORef [OKMeta blk]
 }

data SubConstraints blk = SubConstraints
 {scflip :: IORef Bool,
  sccomcount :: IORef Int,
  scsub1 :: CTree blk,
  scsub2 :: CTree blk
 }


newCTree :: Maybe (CTree blk) -> IO (CTree blk)
newCTree parent = do
 priometa <- newIORef (NoPrio False)
 sub <- newIORef Nothing
 rparent <- newIORef parent
 handles <- newIORef []
 return $ CTree priometa sub rparent handles

newSubConstraints :: CTree blk -> IO (SubConstraints blk)
newSubConstraints node = do
 flip <- newIORef True -- False -- initially (and always) True, trying out prefer rightmost subterm when none have priority
 comcount <- newIORef 0
 sub1 <- newCTree $ Just node
 sub2 <- newCTree $ Just node
 return $ SubConstraints flip comcount sub1 sub2


data PrioMeta blk = forall a . Refinable a blk => PrioMeta Prio (Metavar a blk)
                  | NoPrio Bool -- True if subconstraint is done (all OK)

instance Eq (PrioMeta blk) where
 NoPrio d1 == NoPrio d2 = d1 == d2
 PrioMeta p1 m1 == PrioMeta p2 m2 = p1 == p2 && hequalMetavar m1 m2
 _ == _ = False

-- -----------------------

data Restore = forall a . Restore (IORef a) a

type Undo = StateT [Restore] IO

ureadIORef :: IORef a -> Undo a
ureadIORef ptr = lift $ readIORef ptr

uwriteIORef :: IORef a -> a -> Undo ()
uwriteIORef ptr newval = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ NoUndo.writeIORef ptr newval

umodifyIORef :: IORef a -> (a -> a) -> Undo ()
umodifyIORef ptr f = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ NoUndo.writeIORef ptr (f oldval)

ureadmodifyIORef :: IORef a -> (a -> a) -> Undo a
ureadmodifyIORef ptr f = do
 oldval <- ureadIORef ptr
 modify (Restore ptr oldval :)
 lift $ NoUndo.writeIORef ptr (f oldval)
 return oldval

runUndo :: Undo a -> IO a
runUndo x = do
 (res, restores) <- runStateT x []
 mapM_ (\(Restore ptr oldval) -> NoUndo.writeIORef ptr oldval) restores
 return res

-- -----------------------

newtype RefCreateEnv blk a = RefCreateEnv
  { runRefCreateEnv :: StateT ((IORef [SubConstraints blk]), Int) IO a }

instance Functor (RefCreateEnv blk) where
  fmap f = RefCreateEnv . fmap f . runRefCreateEnv

instance Applicative (RefCreateEnv blk) where
  pure    = RefCreateEnv . pure
  f <*> t = RefCreateEnv $ runRefCreateEnv f <*> runRefCreateEnv t

instance Monad (RefCreateEnv blk) where
  return = pure
  t >>= f = RefCreateEnv $ runRefCreateEnv t >>= runRefCreateEnv . f


newtype Cost = Cost { getCost :: Int }
  deriving (Num, Eq, Ord)

data Move' blk a = Move
  { moveCost :: Cost
  , moveNext :: RefCreateEnv blk a
  }

class Refinable a blk where
 refinements :: blk -> [blk] -> Metavar a blk -> IO [Move' blk a]


newPlaceholder :: RefCreateEnv blk (MM a blk)
newPlaceholder = RefCreateEnv $ do
 (mcompoint, c) <- get
 m <- lift $ newMeta mcompoint
 put (mcompoint, (c + 1))
 return $ Meta m

newOKHandle :: RefCreateEnv blk (OKHandle blk)
newOKHandle = RefCreateEnv $ do
 (e, c) <- get
 cp <- lift $ newIORef []
 m  <- lift $ newMeta cp
 put (e, (c + 1))
 return $ Meta m

dryInstantiate :: RefCreateEnv blk a -> IO a
dryInstantiate bind = evalStateT (runRefCreateEnv bind) (__IMPOSSIBLE__, 0)

type BlkInfo blk = (Bool, Prio, Maybe blk) -- Bool - is principal

data MM a blk = NotM a
              | Meta (Metavar a blk)

rm :: Empty -> MM a b -> a
rm _ (NotM x) = x
rm e Meta{}   = absurd e

type MetaEnv = IO


data MB a blk = NotB a
              | forall b . Refinable b blk => Blocked (Metavar b blk) (MetaEnv (MB a blk))
              | Failed String

data PB blk = NotPB (Prop blk)
            | forall b . Refinable b blk => PBlocked (Metavar b blk) (BlkInfo blk) (MetaEnv (PB blk))
            | forall b1 b2 . (Refinable b1 blk, Refinable b2 blk) => PDoubleBlocked (Metavar b1 blk) (Metavar b2 blk) (MetaEnv (PB blk))

data QPB b blk = QPBlocked (BlkInfo blk) (MetaEnv (PB blk))
               | QPDoubleBlocked (IORef Bool) (MetaEnv (PB blk)) -- flag set True by first observer that continues

mmcase :: Refinable a blk => MM a blk -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mmcase x f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ Blocked m (mmcase x f)

mmmcase :: MM a blk -> MetaEnv (MB b blk) -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mmmcase x fm f = case x of
 NotM x -> f x
 Meta m -> do
  bind <- readIORef $ mbind m
  maybe fm f bind

mmpcase :: Refinable a blk => BlkInfo blk -> MM a blk -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mmpcase blkinfo x f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ PBlocked m blkinfo (mmpcase __IMPOSSIBLE__ x f) -- blkinfo not needed because will be notb next time

doubleblock :: (Refinable a blk, Refinable b blk) => MM a blk -> MM b blk -> MetaEnv (PB blk) -> MetaEnv (PB blk)
doubleblock (Meta m1) (Meta m2) cont = return $ PDoubleBlocked m1 m2 cont
doubleblock _ _ _ = __IMPOSSIBLE__

mbcase :: MetaEnv (MB a blk) -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mbcase x f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ Blocked m (mbcase x f)
  Failed msg -> return $ Failed msg

mbpcase :: Prio -> Maybe blk -> MetaEnv (MB a blk) -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mbpcase prio bi x f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ PBlocked m (False, prio, bi) (mbpcase prio bi x f)
  Failed msg -> return $ NotPB $ Error msg

mmbpcase :: MetaEnv (MB a blk) -> (forall b . Refinable b blk => MM b blk -> MetaEnv (PB blk)) -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mmbpcase x fm f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m _ -> fm (Meta m)
  Failed msg -> return $ NotPB $ Error msg

waitok :: OKHandle blk -> MetaEnv (MB b blk) -> MetaEnv (MB b blk)
waitok okh f =
 mmcase okh $ \ OKVal -> f -- principle constraint is never present for okhandle so it will not be refined

mbret :: a -> MetaEnv (MB a blk)
mbret x = return $ NotB x

mbfailed :: String -> MetaEnv (MB a blk)
mbfailed msg = return $ Failed msg

mpret :: Prop blk -> MetaEnv (PB blk)
mpret p = return $ NotPB p

expandbind :: MM a blk -> MetaEnv (MM a blk)
expandbind x = case x of
 NotM{} -> return x
 Meta m -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> return $ NotM x
   Nothing -> return x


-- -----------------------

type HandleSol = IO ()


type SRes = Either Bool Int

topSearch :: forall blk . IORef Int -> IORef Int -> HandleSol -> blk -> MetaEnv (PB blk) -> Cost -> Cost -> IO Bool
topSearch ticks nsol hsol envinfo p searchdepth depthinterval = do
 depthreached <- newIORef False


 mainroot <- newCTree Nothing

 let
  searchSubProb :: [(CTree blk, Maybe (IORef Bool))] -> Cost -> IO SRes
  searchSubProb [] depth = do
   when (depth < depthinterval) $ do


    hsol
    n <- readIORef nsol
    NoUndo.writeIORef nsol $! n - 1


   return $ Left True
  searchSubProb ((root, firstdone) : restprobs) depth =
   let
    search :: Cost -> IO SRes
    search depth = do
     pm <- readIORef $ ctpriometa root
     case pm of
      NoPrio False -> return $ Left False -- nothing to refine but not done, this can happen when eq constraints are passed along with main constraint in agdaplugin
      NoPrio True ->
       searchSubProb restprobs depth -- ?? what should depth be
      PrioMeta _ m -> do
       let carryon = fork m depth
       sub <- readIORef $ ctsub root
       case sub of
        Nothing -> carryon
        Just sc -> do
         let sub1 = scsub1 sc
             sub2 = scsub2 sc
         pm1 <- readIORef $ ctpriometa sub1
         pm2 <- readIORef $ ctpriometa sub2
         let split = carryon -- split disabled
         case pm1 of
          NoPrio True -> split
          _ ->
           case pm2 of
            NoPrio True -> split
            _ -> do
             comc <- readIORef $ sccomcount sc
             case comc of
              0 -> split
              _ -> carryon

    fork :: forall a. Refinable a blk => Metavar a blk -> Cost -> IO SRes
    fork m depth = do
      blkinfos <- extractblkinfos m
      refs <- refinements envinfo blkinfos m
      f refs
     where
      f :: [Move' blk a] -> IO SRes
      f [] = do
       erefs <- readIORef $ mextrarefs m
       case erefs of
        [] -> return (Left False)
        _ -> do
         NoUndo.writeIORef (mextrarefs m) []
         f erefs
      f (Move cost bind : binds) = hsres (refine m bind (depth - cost)) (f binds)
    hsres :: IO SRes -> IO SRes -> IO SRes
    hsres x1 x2 = do
     res <- x1
     case res of
      Right _ -> return res
      Left found -> do
       n <- readIORef nsol
       if n == 0 then
         return res
        else do
         res2 <- x2
         case res2 of
          Right _ -> if found then __IMPOSSIBLE__ else return res2
          Left found2 -> return $ Left (found || found2)

    refine :: Metavar a blk -> RefCreateEnv blk a -> Cost -> IO SRes

    refine _ _ depthleft | depthleft < 0 = do
     NoUndo.writeIORef depthreached True
     return $ Left False


    refine m bind depthleft = runUndo $
     do t <- ureadIORef ticks
        lift $ NoUndo.writeIORef ticks $! t + 1


        (bind, (_, nnewmeta)) <- lift $ runStateT (runRefCreateEnv bind) (mcompoint m, 0)
        uwriteIORef (mbind m) (Just bind)
        mcomptr <- ureadIORef $ mcompoint m
        mapM_ (\comptr ->
          umodifyIORef (sccomcount comptr) (+ (nnewmeta - 1))
          -- umodifyIORef (scflip comptr) not -- don't flip now since trying prefer rightmost subterm if non have prio
         ) mcomptr
        obs <- ureadIORef (mobs m)
        res <- recalcs obs
        if res
          then
            return $ Left False     -- failed
          else
            lift $ search depthleft -- succeeded

    doit = do
     res <- search depth
     return $ case res of
      Right n ->
       case firstdone of
        Nothing ->
         if n == 0 then
          Left False
         else
          Right (n - 1)
        Just _ ->
         Right (n + 1)
      res@(Left True) -> res
      res@(Left False) ->
       case firstdone of
        Nothing -> res
        Just _ -> Right 0
   in
    case firstdone of
     Nothing -> doit
     Just rdone -> do
      done <- readIORef rdone
      if done then
        searchSubProb restprobs depth
       else do
        NoUndo.writeIORef rdone True
        doit

 runUndo $ do
  res <- reccalc p (Just mainroot)
  if res -- failed immediately
    then
        return False
    else
      do
        Left _solFound <- lift $ searchSubProb [(mainroot, Nothing)] searchdepth
        lift $ readIORef depthreached


extractblkinfos :: Metavar a blk -> IO [blk]
extractblkinfos m = do
 obs <- readIORef $ mobs m
 return $ f obs
 where
  f [] = []
  f ((QPBlocked (_,_,mblkinfo) _, _) : cs) =
   case mblkinfo of
    Nothing -> f cs
    Just blkinfo -> blkinfo : f cs
  f ((QPDoubleBlocked{}, _) : cs) = f cs

recalcs :: [(QPB a blk, Maybe (CTree blk))] -> Undo Bool
recalcs cs = foldr (seqc . recalc) (return False) cs

seqc :: Undo Bool -> Undo Bool -> Undo Bool
seqc x y = do
 res1 <- x
 case res1 of
  res1@True -> return res1
  False -> y

recalc :: (QPB a blk, Maybe (CTree blk)) -> Undo Bool
recalc (con, node) = case con of
  QPBlocked       _    cont -> reccalc cont node
  QPDoubleBlocked flag cont -> do
    fl <- ureadIORef flag
    if fl
      then return False
      else do
        uwriteIORef flag True
        reccalc cont node

reccalc :: MetaEnv (PB blk) -> Maybe (CTree blk) -> Undo Bool
reccalc cont node = do
  res <- calc cont node
  case res of
    Nothing -> return True
    Just pendhandles ->
      foldM
        ( \res1 h ->
            if res1
              then return res1
              else do
                uwriteIORef (mbind h) $ Just OKVal
                obs <- ureadIORef (mobs h)
                recalcs obs
        )
        False
        pendhandles

calc :: forall blk . MetaEnv (PB blk) -> Maybe (CTree blk) -> Undo (Maybe [OKMeta blk])
calc cont node = do
  res <- donewp node cont
  case res of
   Just (_, pendhandles) -> do
    pendhandles2 <- case node of
     Just node -> propagatePrio node
     Nothing -> return []
    return $ Just (pendhandles ++ pendhandles2)
   Nothing -> return Nothing
 where
  storeprio (Just node) pm pendhandles = do
   pendhandles' <- case pm of
    NoPrio True -> do
     handles <- ureadIORef (cthandles node)
     return $ handles ++ pendhandles
    _ -> return pendhandles
   uwriteIORef (ctpriometa node) pm
   return $ Just (pm, pendhandles')
  storeprio Nothing _ _ =
   return $ Just (NoPrio False, [])
  donewp node p = do
   bp <- lift p
   case bp of
    NotPB p ->
     doprop node p
    PBlocked m blkinfo cont -> do
     oldobs <- ureadmodifyIORef (mobs m) ((QPBlocked blkinfo cont, node) :)
     let (princ, prio, _) = blkinfo
     pp <- ureadIORef (mprincipalpresent m)
     when (princ && not pp) $ do
      uwriteIORef (mprincipalpresent m) True
      mapM_ (\(qpb, node) -> case node of
         Just node ->
          case qpb of
           QPBlocked (_, prio, _) _ -> do


            uwriteIORef (ctpriometa node) (PrioMeta prio m)
            propagatePrio node
           QPDoubleBlocked _flag _ ->
            return []
         Nothing -> return []
       ) oldobs
     if pp || princ then
       storeprio node (PrioMeta prio m) []
      else
       storeprio node (NoPrio False) []
    PDoubleBlocked m1 m2 cont -> do
     flag <- lift $ newIORef False

     let newobs :: forall b. [(QPB b blk, Maybe (CTree blk))]
                          -> [(QPB b blk, Maybe (CTree blk))]
         newobs = ((QPDoubleBlocked flag cont, node) :)
     umodifyIORef (mobs m1) newobs
     umodifyIORef (mobs m2) newobs
     storeprio node (NoPrio False) []
  doprop node p =
   case p of
    OK -> storeprio node (NoPrio True) []
    Error _ -> return Nothing


    AddExtraRef _ m eref -> do
     lift $ NoUndo.modifyIORef (mextrarefs m) (eref :)
     return Nothing
    And coms p1 p2 -> do
     let Just jnode = node
     sc <- lift $ newSubConstraints jnode


     uwriteIORef (ctsub jnode) $ Just sc
     ndep <- case coms of
      Nothing -> return 1 -- no metas pointing to it so will never decrement to 0
      Just _coms  -> return 1 -- dito
     lift $ NoUndo.writeIORef (sccomcount sc) ndep -- OK since sc was just created
     resp1 <- donewp (Just $ scsub1 sc) p1
     case resp1 of
      Just (pm1, phs1) -> do
       resp2 <- donewp (Just $ scsub2 sc) p2
       case resp2 of
        Just (pm2, phs2) ->
         storeprio node (choosePrioMeta False pm1 pm2) (phs1 ++ phs2)
        resp2@Nothing -> return resp2
      resp1@Nothing -> return resp1
    Sidecondition sidep mainp -> do
     resp1 <- donewp Nothing sidep
     case resp1 of
      Just{} -> do
       resp2 <- donewp node mainp
       case resp2 of
        Just (pm2, phs2) ->
         storeprio node pm2 phs2
        resp2@Nothing -> return resp2
      resp1@Nothing -> return resp1
    Or prio p1 p2 -> do
     cm <- lift $ initMeta
     donewp node (choose (Meta cm) prio p1 p2)
    ConnectHandle (Meta handle) p' -> do
     let Just jnode = node
     umodifyIORef (cthandles jnode) (handle :)
     donewp node p'
    ConnectHandle (NotM _) _ -> __IMPOSSIBLE__

choosePrioMeta :: Bool -> PrioMeta blk -> PrioMeta blk -> PrioMeta blk
choosePrioMeta flip pm1@(PrioMeta p1 _) pm2@(PrioMeta p2 _)
  | p1 > p2 = pm1
  | p2 > p1 = pm2
  | flip = pm2
  | otherwise = pm1
choosePrioMeta _ pm@(PrioMeta _ _) (NoPrio _) = pm
choosePrioMeta _ (NoPrio _) pm@(PrioMeta _ _) = pm
choosePrioMeta _ (NoPrio d1) (NoPrio d2) = NoPrio (d1 && d2)

propagatePrio :: CTree blk -> Undo [OKMeta blk]
propagatePrio node = do
  parent <- lift $ readIORef $ ctparent node
  case parent of
    Nothing     -> return []
    Just parent -> do
      Just sc <- ureadIORef (ctsub parent)
      pm1     <- ureadIORef $ ctpriometa $ scsub1 sc
      pm2     <- ureadIORef $ ctpriometa $ scsub2 sc
      flip    <- ureadIORef $ scflip sc
      let pm = choosePrioMeta flip pm1 pm2
      opm <- ureadIORef (ctpriometa parent)
      if (pm /= opm)
        then do
          uwriteIORef (ctpriometa parent) pm
          phs <- case pm of
            NoPrio True -> ureadIORef (cthandles parent)
            _           -> return []
          phs2 <- propagatePrio parent
          return $ phs ++ phs2
        else
          return []

data Choice = LeftDisjunct | RightDisjunct

choose :: MM Choice blk -> Prio -> MetaEnv (PB blk) -> MetaEnv (PB blk) -> MetaEnv (PB blk)
choose c prio p1 p2 =
 mmpcase (True, prio, Nothing) c $ \c -> case c of
  LeftDisjunct -> p1
  RightDisjunct -> p2

instance Refinable Choice blk where
 refinements _ _ _ = return $ Move 0 . return <$> [LeftDisjunct, RightDisjunct]


instance Refinable OKVal blk where
 refinements _ _ _ = __IMPOSSIBLE__ -- OKVal should never be refined


-- ------------------------------------
