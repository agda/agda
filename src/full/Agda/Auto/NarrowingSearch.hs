{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}

module Agda.Auto.NarrowingSearch where

import Data.IORef hiding (writeIORef, modifyIORef)
import qualified Data.IORef as NoUndo (writeIORef, modifyIORef)
import Control.Monad.State
import Data.Char


type Prio = Int

class Trav a blk | a -> blk where
 traverse :: Monad m => (forall b . Trav b blk => MM b blk -> m ()) -> a -> m ()

instance Trav a blk => Trav (MM a blk) blk where
 traverse f me = f me

data Term blk = forall a . Trav a blk => Term a

data Prop blk = OK
								      | Error String
								      | And (Maybe [Term blk]) (MetaEnv (PB blk)) (MetaEnv (PB blk))
								      | Or Prio (MetaEnv (PB blk)) (MetaEnv (PB blk))

runProp :: MetaEnv (PB blk) -> MetaEnv ()
runProp x = do
 x <- x
 case x of
  PBlocked _ _ _ _ -> putStr "<blocked>"
  PDoubleBlocked _ _ _ -> putStr "<double blocked>"
  NotPB x -> case x of
   OK -> putStr "OK"
   Error s -> putStr $ "(Error: " ++ s ++ ")"
   And _ x1 x2 -> do
    putStr "(And "
    runProp x1
    putStr " "
    runProp x2
    putStr ")"
   Or _ x1 x2 -> do
    putStr "(Or "
    runProp x1
    putStr " "
    runProp x2
    putStr ")"

data Metavar a blk = Metavar
 {mbind :: IORef (Maybe a),
  mprincipalpresent :: IORef Bool,
  mobs :: IORef [(QPB a blk, CTree blk)],
  mcompoint :: IORef (Maybe (SubConstraints blk))
 }

hequalMetavar :: Metavar a1 blk1 -> Metavar a2 bkl2 -> Bool
hequalMetavar m1 m2 = mprincipalpresent m1 == mprincipalpresent m2

newMeta :: Maybe (SubConstraints blk) -> IO (Metavar a blk)
newMeta mcompoint = do
 bind <- newIORef Nothing
 pp <- newIORef False
 obs <- newIORef []
 cp <- newIORef mcompoint
 return $ Metavar bind pp obs cp

data CTree blk = CTree
 {ctpriometa :: IORef (PrioMeta blk),
  ctsub :: IORef (Maybe (SubConstraints blk)),
  ctparent :: IORef (Maybe (CTree blk))  -- Nothing - root
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
 return $ CTree priometa sub rparent

newSubConstraints :: CTree blk -> IO (SubConstraints blk)
newSubConstraints node = do
 flip <- newIORef False
 comcount <- newIORef 0
 sub1 <- newCTree $ Just node
 sub2 <- newCTree $ Just node
 return $ SubConstraints flip comcount sub1 sub2


data PrioMeta blk = forall a . Refinable a blk => PrioMeta Prio (Metavar a blk)
                  | NoPrio Bool  -- True if subconstraint is done (all OK)

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

type RefCreateEnv blk = StateT (Maybe (SubConstraints blk), Int) IO

class Refinable a blk | a -> blk where
 refinements :: blk -> [blk] -> IO [(Int, RefCreateEnv blk a)]
 printref :: a -> IO String

newPlaceholder :: RefCreateEnv blk (MM a blk)
newPlaceholder = do
 (mcompoint, c) <- get
 put (mcompoint, c + 1)
 m <- lift $ newMeta mcompoint
 return $ Meta m

dryInstantiate :: RefCreateEnv blk a -> IO a
dryInstantiate bind = evalStateT bind (Nothing, 0)

type BlkInfo blk = (Bool, Prio, Maybe blk)  -- Bool - is principal

data MM a blk = NotM a
              | Meta (Metavar a blk)

type MetaEnv = IO

type PrintConstr = MetaEnv String

data MB a blk = NotB a
              | forall b . Refinable b blk => Blocked (Metavar b blk) (MetaEnv (MB a blk))
              | Failed String

data PB blk = NotPB (Prop blk)
            | forall b . Refinable b blk => PBlocked (Metavar b blk) (BlkInfo blk) PrintConstr (MetaEnv (PB blk))
            | forall b . Refinable b blk => PDoubleBlocked (Metavar b blk) (Metavar b blk) (MetaEnv (PB blk))

data QPB b blk = QPBlocked (BlkInfo blk) PrintConstr (MetaEnv (PB blk))
               | QPDoubleBlocked (IORef Bool) (MetaEnv (PB blk))  -- flag set True by first observer that continues

mmcase :: Refinable a blk => MM a blk -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mmcase x f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ Blocked m (mmcase x f)

mmmcase :: Refinable a blk => MM a blk -> MetaEnv (MB b blk) -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mmmcase x fm f = case x of
 NotM x -> f x
 Meta m -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> fm

mmpcase :: Refinable a blk => BlkInfo blk -> MM a blk -> PrintConstr -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mmpcase blkinfo x pr f = case x of
 NotM x -> f x
 x@(Meta m) -> do
  bind <- readIORef $ mbind m
  case bind of
   Just x -> f x
   Nothing -> return $ PBlocked m blkinfo pr (mmpcase (error "blkinfo not needed because will be notb next time") x pr f)

doubleblock :: Refinable a blk => MM a blk -> MM a blk -> MetaEnv (PB blk) -> MetaEnv (PB blk)
doubleblock (Meta m1) (Meta m2) cont = return $ PDoubleBlocked m1 m2 cont
doubleblock _ _ _ = error "doubleblock: this case should not occur"

mbcase :: MetaEnv (MB a blk) -> (a -> MetaEnv (MB b blk)) -> MetaEnv (MB b blk)
mbcase x f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ Blocked m (mbcase x f)
  Failed msg -> return $ Failed msg

mbpcase :: Prio -> MetaEnv (MB a blk) -> PrintConstr -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mbpcase prio x pr f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> return $ PBlocked m (False, prio, Nothing) pr (mbpcase prio x pr f)
  Failed msg -> return $ NotPB $ Error msg

mmbpcase :: MetaEnv (MB a blk) -> MetaEnv (PB blk) -> (a -> MetaEnv (PB blk)) -> MetaEnv (PB blk)
mmbpcase x fm f = do
 x' <- x
 case x' of
  NotB x -> f x
  Blocked m x -> fm
  Failed msg -> return $ NotPB $ Error msg

mbret :: a -> MetaEnv (MB a blk)
mbret x = return $ NotB x

mbfailed :: String -> MetaEnv (MB a blk)
mbfailed msg = return $ Failed msg

mpret :: Prop blk -> MetaEnv (PB blk)
mpret p = return $ NotPB p

-- -----------------------

type HandleSol = IO ()
type HandlePartSol = IO ()

type SRes = Either Bool Int

topSearch :: forall blk . IORef Int -> IORef Int -> HandleSol -> HandlePartSol -> Bool -> blk -> MetaEnv (PB blk) -> Int -> Int -> IO Bool
topSearch ticks nsol hsol hpartsol inter envinfo p depth depthinterval = do
 depthreached <- newIORef False
 exitinteractive <- newIORef False

 let
  searchSubProb :: [(CTree blk, Maybe (IORef Bool))] -> Int -> IO SRes
  searchSubProb [] depth = do
   when (depth < depthinterval) $ do
    hsol
    n <- readIORef nsol
    NoUndo.writeIORef nsol $! n - 1
    when inter (getChar >> return ())
   return $ Left True
  searchSubProb ((root, firstdone) : restprobs) depth =
   let
    search :: Int -> IO SRes
    search depth = do
     pm <- readIORef $ ctpriometa root
     case pm of
      NoPrio False -> error "NarrowingSearch.search: nothing to refine but not done"
      NoPrio True ->
       searchSubProb restprobs depth  -- ?? what should depth be
      PrioMeta _ m -> do
       let carryon = (if inter then forki else fork) m depth
       sub <- readIORef $ ctsub root
       case sub of
        Nothing -> carryon
        Just sc -> do
         let sub1 = scsub1 sc
             sub2 = scsub2 sc
         pm1 <- readIORef $ ctpriometa sub1
         pm2 <- readIORef $ ctpriometa sub2
         let split = carryon  -- split disabled
         {-let split = runUndo $ do
              uwriteIORef (ctparent sub1) Nothing
              uwriteIORef (ctparent sub2) Nothing
              done <- lift $ newIORef False
              flip <- lift $ readIORef $ scflip sc
              let pmmax = choosePrioMeta flip pm1 pm2
              if pmmax == pm1 then
                lift $ searchSubProb ((sub1, Nothing) : (sub2, Just done) : restprobs) depth  -- ?? what should depth be
               else
                lift $ searchSubProb ((sub2, Nothing) : (sub1, Just done) : restprobs) depth  -- ?? what should depth be-}
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

    fork :: Refinable a blk => Metavar a blk -> Int -> IO SRes
    fork m depth = do
      blkinfos <- extractblkinfos m
      refs <- refinements envinfo blkinfos
      f refs
     where
      f [] = return (Left False)
      f ((cost, bind) : binds) = hsres (refine m bind (depth - cost)) (f binds)

    forki :: Refinable a blk => Metavar a blk -> Int -> IO SRes
    forki m depth = do
     blkinfos <- extractblkinfos m
     refs <- refinements envinfo blkinfos
     direfs <- mapM dryInstantiate (map snd refs)
     descs <- mapM printref direfs
     let loop deflt = do
          putStr "\x1b[2J\x1b[0;0H"
          printCTree root >> putStrLn ""
          putStrLn $ "depth: " ++ show depth
          hpartsol
          putStrLn "----------------------------------------------"
          obs <- readIORef (mobs m)
          let pqpb (QPBlocked _ pr _) = pr
              pqpb (QPDoubleBlocked _ _) = return "double blocked"
          mapM_ (\obs -> do
            pc <- pqpb $ fst obs
            putStrLn pc
           ) obs
          putStrLn "----------------------------------------------"
          mapM_ (\(desc, (cost, i)) ->
            putStrLn $ (if i == deflt then "*" else " ") ++ show (i + 1) ++ ": " ++ desc ++ " (" ++ show cost ++ ")"
           ) (zip descs (zip (map fst refs) [0..]))
          when (deflt == length descs) $ putStrLn "* : BACK"
          putStr "<"
          c <- getChar
          putStrLn "\n"
          case c of
           _ | isDigit c ->
            let choice = ord c - ord '1'
            in  hsres (refine m (snd $ refs !! choice) (depth - fst (refs !! choice))) $ do
             e <- readIORef exitinteractive
             if not e then
               loop (choice + 1)
              else
               return $ Left False
           '\x7f' -> return (Left False)
           '\x1b' -> do NoUndo.writeIORef exitinteractive True
                        return (Left False)
           '\n' -> if deflt == length descs then
                    return (Left False)
                   else
                    hsres (refine m (snd $ refs !! deflt) (depth - fst (refs !! deflt))) $ do
                     e <- readIORef exitinteractive
                     if not e then
                       loop (deflt + 1)
                      else
                       return $ Left False
           _ -> error $ "unknown char: " ++ show (ord c)
     loop 0

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
          Right _ -> if found then error "hsres: this should not happen" else return res2
          Left found2 -> return $ Left (found || found2)

    refine :: Metavar a blk -> RefCreateEnv blk a -> Int -> IO SRes
    refine _ _ depth | depth < 0 = do
     NoUndo.writeIORef depthreached True
     return $ Left False
    refine m bind depth = runUndo $
     do mcomptr <- ureadIORef (mcompoint m)
        t <- lift $ readIORef ticks
        lift $ NoUndo.writeIORef ticks $! t + 1
        (bind, (_, nnewmeta)) <- lift $ runStateT bind (mcomptr, 0)

{-
        ob <- ureadIORef (mbind m)
        case ob of
         Just _ -> error "meta already bound"
         Nothing -> return ()
-}

        uwriteIORef (mbind m) (Just bind)
        case mcomptr of
         Nothing -> return ()
         Just comptr -> do
          umodifyIORef (sccomcount comptr) (+ (nnewmeta - 1))
          umodifyIORef (scflip comptr) not
        obs <- ureadIORef (mobs m)
        res <- recalcs obs
        case res of
         True ->  -- failed
          return $ Left False
         False -> lift $ search depth  -- succeeded

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

 root <- newCTree Nothing
 runUndo $ do
  res <- reccalc p root
  case res of
   True ->  -- failed immediately
    return False
   False -> do
    Left solfound <- lift $ searchSubProb [(root, Nothing)] depth
    dr <- lift $ readIORef depthreached
    return dr

extractblkinfos :: Metavar a blk -> IO [blk]
extractblkinfos m = do
 obs <- readIORef $ mobs m
 return $ f obs
 where
  f [] = []
  f ((QPBlocked (_,_,mblkinfo) _ _, _) : cs) =
   case mblkinfo of
    Nothing -> f cs
    Just blkinfo -> blkinfo : f cs
  f ((QPDoubleBlocked _ _, _) : cs) = f cs

recalcs :: [(QPB a blk, CTree blk)] -> Undo Bool
recalcs [] = return False
recalcs (c : cs) = seqc (recalc c) (recalcs cs)

seqc :: Undo Bool -> Undo Bool -> Undo Bool
seqc x y = do
 res1 <- x
 case res1 of
  res1@True -> return res1
  False -> y

recalc :: (QPB a blk, CTree blk) -> Undo Bool
recalc (con, node) =
 case con of
  QPBlocked _ _ cont -> reccalc cont node
  QPDoubleBlocked flag cont -> do
   fl <- ureadIORef flag
   if fl then
     return False
    else do
     uwriteIORef flag True
     reccalc cont node

reccalc :: MetaEnv (PB blk) -> CTree blk -> Undo Bool
reccalc cont node = calc cont node

calc :: forall blk . MetaEnv (PB blk) -> CTree blk -> Undo Bool
calc cont node = do
  res <- donewp node cont
  case res of
   Just _ -> do
    propagatePrio node
    return False
   Nothing -> return True
 where
  storeprio node pm = do
   uwriteIORef (ctpriometa node) pm
   return $ Just pm
  donewp node p = do
   bp <- lift p
   case bp of
    NotPB p ->
     doprop node p
    PBlocked m blkinfo pr cont -> do
     oldobs <- ureadmodifyIORef (mobs m) ((QPBlocked blkinfo pr cont, node) :)
     let (princ, prio, _) = blkinfo
     if princ then do
       uwriteIORef (mprincipalpresent m) True
       mapM_ (\(qpb, node) -> do
         let priometa = case qpb of
                      QPBlocked (_, prio, _) _ _ -> PrioMeta prio m
                      QPDoubleBlocked _ _ -> NoPrio False
         uwriteIORef (ctpriometa node) priometa
         propagatePrio node
        ) oldobs
       storeprio node (PrioMeta prio m)
      else do
       pp <- ureadIORef (mprincipalpresent m)
       if pp then
         storeprio node (PrioMeta prio m)
        else
         storeprio node (NoPrio False)
    PDoubleBlocked m1 m2 cont -> do
     flag <- lift $ newIORef False
     let newobs = ((QPDoubleBlocked flag cont, node) :)
     umodifyIORef (mobs m1) newobs
     umodifyIORef (mobs m2) newobs
     storeprio node (NoPrio False)
  doprop node p =
   case p of
    OK -> storeprio node (NoPrio True)
    Error _ -> return Nothing
    And coms p1 p2 -> do
     sc <- lift $ newSubConstraints node

{-
     osc <- ureadIORef (ctsub node)
     case osc of
      Just _ -> error "sc already set"
      Nothing -> return ()
-}

     uwriteIORef (ctsub node) $ Just sc
     ndep <- case coms of
      Nothing -> return 1  -- no metas pointing to it so will never decrement to 0
      Just coms ->
       liftM snd $ runStateT (mapM_ (\(Term x) ->
         let f :: forall b . Trav b blk => MM b blk -> StateT Int Undo ()
             f (NotM x) = traverse f x
             f (Meta m) = do
              mcomptr <- lift $ ureadIORef (mcompoint m)
              case mcomptr of
               Just _ -> return ()
               Nothing -> do
                bind <- lift $ ureadIORef $ mbind m
                case bind of
                 Just x -> traverse f x
                 Nothing -> do
                  lift $ uwriteIORef (mcompoint m) $ Just sc
                  modify (+1)
         in  traverse f x
        ) coms) 0
     lift $ NoUndo.writeIORef (sccomcount sc) ndep  -- OK since sc was just created
     resp1 <- donewp (scsub1 sc) p1
     case resp1 of
      Just pm1 -> do
       resp2 <- donewp (scsub2 sc) p2
       case resp2 of
        Just pm2 ->
         storeprio node (choosePrioMeta False pm1 pm2)
        resp2@Nothing -> return resp2
      resp1@Nothing -> return resp1
    Or prio p1 p2 -> do
     cm <- lift $ newMeta Nothing
     donewp node (choose (Meta cm) prio p1 p2)

choosePrioMeta :: Bool -> PrioMeta blk -> PrioMeta blk -> PrioMeta blk
choosePrioMeta flip pm1@(PrioMeta p1 _) pm2@(PrioMeta p2 _) = if p1 > p2 then pm1 else if p2 > p1 then pm2 else if flip then pm2 else pm1
choosePrioMeta _ pm@(PrioMeta _ _) (NoPrio _) = pm
choosePrioMeta _ (NoPrio _) pm@(PrioMeta _ _) = pm
choosePrioMeta _ (NoPrio d1) (NoPrio d2) = NoPrio (d1 && d2)

propagatePrio :: CTree blk -> Undo ()
propagatePrio node = do
 parent <- lift $ readIORef $ ctparent node
 case parent of
  Nothing -> return ()
  Just parent -> do
   Just sc <- ureadIORef (ctsub parent)
   pm1 <- ureadIORef $ ctpriometa $ scsub1 sc
   pm2 <- ureadIORef $ ctpriometa $ scsub2 sc
   flip <- ureadIORef $ scflip sc
   let pm = choosePrioMeta flip pm1 pm2
   opm <- ureadIORef (ctpriometa parent)
   if (not (pm == opm)) then do
     uwriteIORef (ctpriometa parent) pm
     propagatePrio parent
    else
     return ()

data Choice = LeftDisjunct | RightDisjunct

choose :: MM Choice blk -> Prio -> MetaEnv (PB blk) -> MetaEnv (PB blk) -> MetaEnv (PB blk)
choose c prio p1 p2 =
 mmpcase (True, prio, Nothing) c (return "choose") $ \c -> case c of
  LeftDisjunct -> p1
  RightDisjunct -> p2

instance Refinable Choice blk where
 refinements _ _ = return [(0, return LeftDisjunct), (0, return RightDisjunct)]  -- no cost to make a choice
 printref LeftDisjunct = return "choose_left"
 printref RightDisjunct = return "choose_right"

-- ------------------------------------

printCTree :: CTree blk -> IO ()
printCTree t = do
 pm <- readIORef $ ctpriometa t
 sub <- readIORef $ ctsub t
 putStr "("
 putStr $ case pm of
  NoPrio False -> "-"
  NoPrio True -> "x"
  PrioMeta p _ -> show p
 case sub of
  Nothing -> return ()
  Just sc -> do
   flip <- readIORef $ scflip sc
   ct <- readIORef $ sccomcount sc
   putStr ", "
   putStr $ if flip then ">" else "<"
   putStr ", "
   putStr $ show ct
   putStr ", "
   printCTree $ scsub1 sc
   putStr ", "
   printCTree $ scsub2 sc
 putStr ")"

