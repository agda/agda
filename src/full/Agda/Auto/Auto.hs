
module Agda.Auto.Auto
      (auto
      , AutoResult(..)
      , AutoProgress(..)
      ) where

import Prelude hiding ((!!), null)

import Control.Monad          ( filterM, forM, guard, join, when )
import Control.Monad.Except
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.State

import qualified Data.List as List
import qualified Data.Map as Map
import Data.IORef
import qualified System.Timeout
import Data.Maybe
import qualified Data.Traversable as Trav
import qualified Data.HashMap.Strict as HMap

import Agda.Utils.Permutation (permute, takeP)
import Agda.TypeChecking.Monad hiding (withCurrentModule)
import Agda.TypeChecking.Telescope
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty (prettyA)
import qualified Agda.Syntax.Concrete.Name as C
import qualified Text.PrettyPrint as PP
import qualified Agda.TypeChecking.Pretty as TCM
import Agda.Syntax.Position
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcreteScope, abstractToConcrete_, runAbsToCon, toConcrete)
import Agda.Interaction.Base
import Agda.Interaction.BasicOps hiding (refine)
import Agda.TypeChecking.Reduce (normalise)
import Agda.Syntax.Common
import qualified Agda.Syntax.Scope.Base as Scope
import Agda.Syntax.Scope.Monad (withCurrentModule)
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.TypeChecking.Monad.Base as TCM
import Agda.TypeChecking.EtaContract (etaContract)

import Agda.Auto.Options
import Agda.Auto.Convert
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl
import Agda.Auto.Typecheck

import Agda.Auto.CaseSplit

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Tuple


insertAbsurdPattern :: String -> String
insertAbsurdPattern [] = []
insertAbsurdPattern s@(_:_) | take (length abspatvarname) s == abspatvarname = "()" ++ drop (length abspatvarname) s
insertAbsurdPattern (c:s) = c : insertAbsurdPattern s

getHeadAsHint :: A.Expr -> Maybe Hint
getHeadAsHint (A.ScopedExpr _ e) = getHeadAsHint e
getHeadAsHint (A.Def qname)      = Just $ Hint False qname
getHeadAsHint (A.Proj _ qname)   = Just $ Hint False $ AN.headAmbQ qname
getHeadAsHint (A.Con qname)      = Just $ Hint True  $ AN.headAmbQ qname
getHeadAsHint _ = Nothing

-- | Result type: Progress & potential Message for the user
--
--   The  of the Auto tactic can be one of the following three:
--
--   1. @Solutions [(ii,s)]@
--      A list of solutions @s@ for interaction ids @ii@.
--      In particular, @Solutions []@ means Agsy found no solution.
--
--   2. @FunClauses cs@
--      A list of clauses for the interaction id @ii@ in which Auto
--      was invoked with case-splitting turned on.
--
--   3. @Refinement s@
--      A refinement for the interaction id @ii@ in which Auto was invoked.

data AutoProgress =
    Solutions  [(InteractionId, String)]
  | FunClauses [String]
  | Refinement String

data AutoResult = AutoResult
  { autoProgress :: AutoProgress
  , autoMessage  :: Maybe String
  }

stopWithMsg :: String -> TCM AutoResult
stopWithMsg msg = return $ AutoResult (Solutions []) (Just msg)

-- | Entry point for Auto tactic (Agsy).
--
--   If the @autoMessage@ part of the result is set to @Just msg@, the
--   message @msg@ produced by Agsy should be displayed to the user.

{-# SPECIALIZE auto :: InteractionId -> Range -> String -> TCM AutoResult #-}
auto
  :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm AutoResult
auto ii rng argstr = liftTCM $ locallyTC eMakeCase (const True) $ do

  -- Parse hints and other configuration.
  let autoOptions = parseArgs argstr
  let hints    = autoOptions ^. aoHints
  let timeout  = autoOptions ^. aoTimeOut
  let pick     = autoOptions ^. aoPick
  let mode     = autoOptions ^. aoMode
  let hintmode = autoOptions ^. aoHintMode
  ahints <- case mode of
    MRefine{} -> return []
    _         -> mapM (parseExprIn ii rng) hints
  let failHints = stopWithMsg "Hints must be a list of constant names"

  eqstuff <- getEqCombinators ii rng

  caseMaybe (mapM getHeadAsHint ahints) failHints $ \ ehints -> do

    -- Get the meta variable for the interaction point we are trying to fill.
    -- Add the @autohints@ for that meta to the hints collection.
    mi <- lookupInteractionId ii
    thisdefinfo <- findClauseDeep ii
    ehints <- (ehints ++) <$> do autohints hintmode mi $ fmap fst3 thisdefinfo

    -- If @thisdefinfo /= Nothing@ get the its type (normalized).
    mrectyp <- maybeToList <$> do
      Trav.forM thisdefinfo $ \ (def, _, _) -> do
        normalise =<< do TCM.defType <$> getConstInfo def

    (myhints', mymrectyp, tccons, eqcons, cmap) <- tomy mi (ehints ++ eqstuff) mrectyp

    let (myhints, c1to6) = splitAt (length myhints' - length eqstuff) myhints'
        meqr = ifNull eqstuff Nothing $ \ _ -> {- else -}
                 let [c1, c2, c3, c4, c5, c6] = c1to6
                 in  Just $ EqReasoningConsts c1 c2 c3 c4 c5 c6


    let tcSearchSC isdep ctx typ trm = caseMaybe meqr a $ \ eqr ->
          mpret $ Sidecondition (calcEqRState eqr trm) a
          where a = tcSearch isdep ctx typ trm

    let (mainm, _, _, _) = tccons Map.! mi
    case mode of
     MNormal listmode disprove -> do
        let numsols = if listmode then 10 else 1
          -- Andreas, 2015-05-17 Issue 1504:
          -- wish to produce several solutions, as
          -- the first one might be ill-typed.
          -- However, currently changing the 1 to something higher makes Agsy loop.
        sols <- liftIO $ newIORef ([] :: [[I.Term]])
        nsol <- liftIO $ newIORef $ pick + numsols
        let hsol = do
             nsol' <- readIORef nsol
             let cond = nsol' <= numsols
             when cond $ do
               trms <- runExceptT
                       $ mapM (\ (m , _, _, _) -> convert (Meta m) :: MOT I.Term)
                       $ Map.elems tccons
               case trms of
                 Left{}     -> writeIORef nsol $! nsol' + 1
                 Right trms -> modifyIORef sols (trms :)
                 -- Right trms -> if listmode then modifyIORef sols (trms :)
                 --                           else writeIORef sols [trms]
        ticks <- liftIO $ newIORef 0

        let exsearch initprop recinfo defdfv =
             liftIO $ System.Timeout.timeout (getTimeOut timeout * 1000)
                    $ loop 0
             where
               loop d = do
                 let rechint x = case recinfo of
                                  Nothing -> x
                                  Just (_, recdef) -> (recdef, HMRecCall) : x
                     env = RIEnv { rieHints             = rechint $ map (,HMNormal) myhints
                                 , rieDefFreeVars       = defdfv
                                 , rieEqReasoningConsts = meqr
                                 }
                 depreached <- topSearch ticks nsol hsol env (initprop) d costIncrease
                 nsol' <- readIORef nsol
                 if nsol' /= 0 && depreached then loop (d + costIncrease) else return depreached

        let getsols :: [I.Term] -> TCM [(MetaId, A.Expr)]
            getsols sol = do
             exprs <- forM (zip (Map.keys tccons) sol) $ \ (mi, e) -> do
               mv   <- lookupLocalMetaAuto mi
               e    <- etaContract e
               expr <- modifyAbstractExpr <$> do withMetaInfo (getMetaInfo mv) $ reify e
               return (mi, expr)

             let loop :: I.MetaId -> StateT [I.MetaId] TCM [(I.MetaId, A.Expr)]
                 loop midx = do
                   let (m, _, _, deps) = tccons Map.! midx
                   asolss <- mapM loop deps
                   dones  <- get
                   asols  <- if midx `elem` dones then return [] else do
                     put (midx : dones)
                     return [(midx, fromMaybe __IMPOSSIBLE__ $ lookup midx exprs)]
                   return $ concat asolss ++ asols
             (asols, _) <- runStateT (loop mi) []
             return asols

        if disprove then
          case eqcons of
           [] -> case Map.elems tccons of
            (m, mytype, mylocalVars, _) : [] -> do
                defdfv <- case thisdefinfo of
                           Just (def, _, _) -> getdfv mi def
                           Nothing -> return 0
                ee <- liftIO $ newIORef $ ConstDef {cdname = "T", cdorigin = __IMPOSSIBLE__, cdtype = NotM $ Sort (Set 0), cdcont = Postulate, cddeffreevars = 0}
                let (restargs, modargs) = splitAt (length mylocalVars - defdfv) mylocalVars
                    mytype' = foldl (\x y -> NotM $ Pi Nothing NotHidden (freeIn 0 y) y (Abs NoId x)) mytype restargs
                    htyp = negtype ee mytype'
                    sctx = (Id "h", closify htyp) : map (\x -> (NoId, closify x)) modargs
                    ntt = closify (NotM $ App Nothing (NotM OKVal) (Const ee) (NotM ALNil))
                res <- exsearch (tcSearchSC False sctx ntt (Meta m)) Nothing defdfv
                rsols <- fmap reverse $ liftIO $ readIORef sols
                if null rsols then do
                  nsol' <- liftIO $ readIORef nsol
                  stopWithMsg $ insuffsols (pick + numsols - nsol')
                 else do
                  aexprss <- mapM getsols rsols
                  cexprss <- forM aexprss $ mapM $ \(mi, e) -> do
                    mv <- lookupLocalMetaAuto mi
                    withMetaInfo (getMetaInfo mv) $ do
                      (mi,) <$> abstractToConcrete_ e
                  let ss = dropWhile (== ' ') . dropWhile (/= ' ') . prettyShow
                      disp [(_, cexpr)] = ss cexpr
                      disp cexprs = concatMap (\ (mi, cexpr) -> ss cexpr ++ " ") cexprs
                  ticks <- liftIO $ readIORef ticks
                  stopWithMsg $ unlines $
                    ("Listing disproof(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1)) :
                    for (zip cexprss [pick..]) (\ (x, y) -> show y ++ "  " ++ disp x)
            _ -> stopWithMsg "Metavariable dependencies not allowed in disprove mode"
           _ -> stopWithMsg "Metavariable dependencies not allowed in disprove mode"
         else do
          (recinfo, defdfv) <-
           case thisdefinfo of
            Just (def, clause, _) -> do
             let [rectyp'] = mymrectyp
             defdfv <- getdfv mi def
             myrecdef <- liftIO $ newIORef $ ConstDef {cdname = "", cdorigin = (Nothing, def), cdtype = rectyp', cdcont = Postulate, cddeffreevars = defdfv}
             (_, pats) <- constructPats cmap mi clause
             defdfv <- getdfv mi def
             return $ if contains_constructor pats then
               (Just (pats, myrecdef), defdfv)
              else
               (Nothing, defdfv)
            Nothing -> return (Nothing, 0)
          let tc (m, mytype, mylocalVars) isdep = tcSearchSC isdep (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) (Meta m)
              initprop =
                foldl (\x (ineq, e, i) -> mpret $ And Nothing x (comp' ineq (closify e) (closify i)))
                 (foldl (\x (m, mt, mlv, _) ->
                   if hequalMetavar m mainm then
                    case recinfo of
                     Just (recpats, recdef) ->
                      mpret $ Sidecondition (localTerminationSidecond (localTerminationEnv recpats) recdef (Meta m))
                                            (tc (m, mt, mlv) False)
                     Nothing -> mpret $ And Nothing x (tc (m, mt, mlv) False)
                   else
                    mpret $ And Nothing x (tc (m, mt, mlv) True)
                  )
                  (mpret OK)
                  (Map.elems tccons)
                 ) eqcons
          res <- exsearch initprop recinfo defdfv
          riis <- map swap <$> getInteractionIdsAndMetas
          let timeoutString | isNothing res = " after timeout (" ++ show timeout ++ "ms)"
                            | otherwise     = ""
          if listmode then do
            rsols <- fmap reverse $ liftIO $ readIORef sols
            if null rsols then do
              nsol' <- liftIO $ readIORef nsol
              stopWithMsg $ insuffsols (pick + numsols - nsol') ++ timeoutString
             else do
              aexprss <- mapM getsols rsols
              -- cexprss <- mapM (mapM (\(mi, e) -> lookupMeta mi >>= \mv -> withMetaInfo (getMetaInfo mv) $ abstractToConcrete_ e >>= \e' -> return (mi, e'))) aexprss
              cexprss <- forM aexprss $ do
                mapM $ \ (mi, e) -> do
                  mv <- lookupLocalMetaAuto mi
                  withMetaInfo (getMetaInfo mv) $ do
                    e' <- abstractToConcrete_ e
                    return (mi, e')
              let disp [(_, cexpr)] = prettyShow cexpr
                  disp cexprs = concat $ for cexprs $ \ (mi, cexpr) ->
                    maybe (show mi) show (lookup mi riis)
                      ++ " := " ++ prettyShow cexpr ++ " "
              ticks <- liftIO $ readIORef ticks
              stopWithMsg $ "Listing solution(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ timeoutString ++
                        "\n" ++ unlines (zipWith (\x y -> show y ++ "  " ++ disp x) cexprss [pick..])
           else {- not listmode -}
            case res of
             Nothing -> do
              nsol' <- liftIO $ readIORef nsol
              stopWithMsg $ insuffsols (pick + numsols - nsol') ++ timeoutString
             Just depthreached -> do
              ticks <- liftIO $ readIORef ticks
              rsols <- liftIO $ readIORef sols
              case rsols of
                [] -> do
                  nsol' <- liftIO $ readIORef nsol
                  stopWithMsg $ insuffsols (pick + numsols - nsol')
                terms -> loop terms where
                  -- Andreas, 2015-05-17  Issue 1504
                  -- If giving a solution failed (e.g. ill-typed)
                  -- we could try the next one.
                  -- However, currently @terms@ is always a singleton list.
                  -- Thus, the following @loop@ is not doing something very
                  -- meaningful.
                  loop :: [[I.Term]] -> TCM AutoResult
                  loop [] = return $ AutoResult (Solutions []) (Just "")
                  loop (term : terms') = do
                    -- On exception, try next solution
                    flip catchError (\ e -> do reportSDoc "auto" 40 $ "Solution failed:" TCM.<?> TCM.prettyTCM e
                                               loop terms') $ do
                      exprs <- getsols term
                      reportSDoc "auto" 20 $ "Trying solution " TCM.<+> TCM.prettyTCM exprs
                      giveress <- forM exprs $ \ (mi, expr0) -> do
                        let expr = killRange expr0
                        case lookup mi riis of
                         Nothing ->
                          -- catchError
                           (giveExpr WithoutForce Nothing mi expr >> return (Nothing, Nothing))
                           -- (const retry)
                           -- (\_ -> return (Nothing, Just ("Failed to give expr for side solution of " ++ show mi)))
                         Just ii' -> do ae <- give WithoutForce ii' Nothing expr
                                        mv <- lookupLocalMetaAuto mi
                                        let scope = getMetaScope mv
                                        ce <- abstractToConcreteScope scope ae
                                        let cmnt = if ii' == ii then agsyinfo ticks else ""
                                        return (Just (ii', prettyShow ce ++ cmnt), Nothing)
                           -- Andreas, 2015-05-17, Issue 1504
                           -- When Agsy produces an ill-typed solution, return nothing.
                           -- TODO: try other solution.
                           -- `catchError` const retry -- (return (Nothing, Nothing))
                      let msg = if length exprs == 1 then
                                 Nothing
                                else
                                 Just $ "Also gave solution(s) for hole(s)" ++
                                         concatMap (\(mi', _) ->
                                          if mi' == mi then "" else (" " ++ case lookup mi' riis of {Nothing -> show mi'; Just ii -> show ii})
                                         ) exprs
                      let msgs = catMaybes $ msg : map snd giveress
                          msg' = unlines msgs <$ guard (not $ null msgs)
                      return $ AutoResult (Solutions $ mapMaybe fst giveress) msg'

     MCaseSplit -> do
      case thisdefinfo of
       Just (def, clause, True) ->
        case Map.elems tccons of
         [(m, mytype, mylocalVars, _)] | null eqcons -> do
          (ids, pats) <- constructPats cmap mi clause
          let ctx = zipWith (\(hid, id) t -> HI hid (id, t)) ids mylocalVars
          ticks <- liftIO $ newIORef 0
          let [rectyp'] = mymrectyp
          defdfv <- getdfv mi def
          myrecdef <- liftIO $ newIORef $ ConstDef {cdname = "", cdorigin = (Nothing, def), cdtype = rectyp', cdcont = Postulate, cddeffreevars = defdfv}
          sols <- liftIO $ System.Timeout.timeout (getTimeOut timeout * 1000) (
             let r d = do
                  sols <- liftIO $ caseSplitSearch ticks __IMPOSSIBLE__ myhints meqr __IMPOSSIBLE__ d myrecdef ctx mytype pats
                  case sols of
                   [] -> r (d + costIncrease)
                   (_:_) -> return sols
             in r 0)
          case sols of
           Just (cls : _) -> withInteractionId ii $ do
            cls' <- liftIO $ runExceptT (mapM frommyClause cls)
            case cls' of
             Left{} -> stopWithMsg "No solution found"
             Right cls' -> do
              cls'' <- forM cls' $ \ (I.Clause _ _ tel ps body t catchall exact recursive reachable ell wm) -> do
                withCurrentModule (AN.qnameModule def) $ do
                 -- Normalise the dot patterns
                 ps <- addContext tel $ normalise ps
                 body <- etaContract body
                 fmap modifyAbstractClause $ inTopContext $ reify $ AN.QNamed def $ I.Clause noRange noRange tel ps body t catchall exact recursive reachable ell wm
              moduleTel <- lookupSection (AN.qnameModule def)
              pcs <- withInteractionId ii $ inTopContext $ addContext moduleTel $ mapM prettyA cls''
              ticks <- liftIO $ readIORef ticks


              return $ AutoResult (FunClauses $ map (insertAbsurdPattern . PP.renderStyle (PP.style { PP.mode = PP.OneLineMode })) pcs) Nothing

           Just [] -> stopWithMsg "No solution found" -- case not possible at the moment because case split doesnt care about search exhaustiveness
           Nothing -> stopWithMsg $ "No solution found at time out (" ++ show timeout ++ "s)"
         _ -> stopWithMsg "Metavariable dependencies not allowed in case split mode"
       _ -> stopWithMsg "Metavariable is not at top level of clause RHS"

     MRefine listmode -> do
      mv <- lookupLocalMetaAuto mi
      let tt = jMetaType $ mvJudgement mv
          minfo = getMetaInfo mv
      targettyp <- withMetaInfo minfo $ do
       vs <- getContextArgs
       targettype <- tt `piApplyM` permute (takeP (length vs) $ mvPermutation mv) vs
       normalise targettype
      let tctx = length $ envContext $ clEnv minfo

      hits <- if "-a" `elem` hints then do
        st <- liftTCM $ join $ pureTCM $ \st _ -> return st
        let defs = st^.stSignature.sigDefinitions
            idefs = st^.stImports.sigDefinitions
            alldefs = HMap.keys defs ++ HMap.keys idefs
        catMaybes <$> mapM (\n ->
          case thisdefinfo of
           Just (def, _, _) | def == n -> return Nothing
           _ -> do
            cn <- withMetaInfo minfo $ runAbsToCon $ toConcrete n
            if C.isInScope cn == C.NotInScope then
              return Nothing
            else getConstInfo' n >>= \case
              Left{} -> return Nothing
              Right c -> do
                ctyp <- normalise $ defType c
                cdfv <- withMetaInfo minfo $ getDefFreeVars n
                return $ case matchType cdfv tctx ctyp targettyp of
                  Nothing -> Nothing
                  Just score -> Just (prettyShow cn, score)
         ) alldefs
       else do
        let scopeinfo = clScope (getMetaInfo mv)
            namespace = Scope.everythingInScope scopeinfo
            names = Scope.nsNames namespace
            qnames = map (\(x, y) -> (x, Scope.anameName $ head y)) $ Map.toList names
            modnames = case thisdefinfo of
                        Just (def, _, _) -> filter (\(_, n) -> n /= def) qnames
                        Nothing -> qnames
        catMaybes <$> mapM (\(cn, n) -> getConstInfo' n >>= \case
          Left{} -> return Nothing
          Right c -> do
            ctyp <- normalise $ defType c
            cdfv <- withMetaInfo minfo $ getDefFreeVars n
            return $ case matchType cdfv tctx ctyp targettyp of
              Nothing -> Nothing
              Just score -> Just (prettyShow cn, score)
         ) modnames

      let sorthits = List.sortBy (\(_, (pa1, pb1)) (_, (pa2, pb2)) -> case compare pa2 pa1 of {EQ -> compare pb1 pb2; o -> o}) hits
      if listmode || pick == (-1) then
        let pick' = max 0 pick
        in if pick' >= length sorthits then
             stopWithMsg $ insuffcands $ length sorthits
            else
             let showhits = take 10 $ drop pick' sorthits
             in stopWithMsg $ "Listing candidate(s) " ++ show pick' ++ "-" ++ show (pick' + length showhits - 1) ++ " (found " ++ show (length sorthits) ++ " in total)\n" ++
                           unlines (zipWith (\i (cn, _) -> show i ++ "  " ++ cn) [pick'..pick' + length showhits - 1] showhits)
       else
        if pick >= length sorthits then
         stopWithMsg $ insuffcands $ length sorthits
        else
         return $ AutoResult (Refinement $ fst $ sorthits !! pick) Nothing
  where
    agsyinfo ticks = ""

-- Get the functions and axioms defined in the same module as @def@.
autohints :: AutoHintMode -> I.MetaId -> Maybe AN.QName -> TCM [Hint]
autohints AHMModule mi (Just def) = do
  scope <- clScope . getMetaInfo <$> lookupLocalMetaAuto mi
  let names     = Scope.nsNames $ Scope.everythingInScope scope
      qnames    = map (Scope.anameName . head) $ Map.elems names
      modnames  = filter (\n -> AN.qnameModule n == AN.qnameModule def && n /= def) qnames
  map (Hint False) <$> do
    (`filterM` modnames) $ \ n -> getConstInfo' n >>= \case
      Left{} -> return False
      Right c -> case theDef c of
        Axiom{}    -> return True
        AbstractDefn{} -> return True
        Function{} -> return True
        _          -> return False

autohints _ _ _ = return []



-- | Names for the equality reasoning combinators
--   Empty if any of these names is not defined.

getEqCombinators :: InteractionId -> Range -> TCM [Hint]
getEqCombinators ii rng = do
  let eqCombinators = ["_≡_", "begin_", "_≡⟨_⟩_", "_∎", "sym", "cong"]
  raw <- mapM (parseExprIn ii rng) eqCombinators `catchError` const (pure [])
  return $ fromMaybe [] $ mapM getHeadAsHint raw

-- | Templates for error messages

genericNotEnough :: String -> Int -> String
genericNotEnough str n = unwords $ case n of
  0 -> ["No", str, "found"]
  1 -> ["Only 1", str, "found"]
  _ -> ["Only", show n, str ++ "s", "found"]

insuffsols :: Int -> String
insuffsols  = genericNotEnough "solution"

insuffcands :: Int -> String
insuffcands = genericNotEnough "candidate"
