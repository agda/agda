{-# LANGUAGE CPP #-}

module Agda.Auto.Auto (auto) where

import Prelude hiding (null)

import Control.Monad.State
import Data.List hiding (null)
import qualified Data.Map as Map
import Data.IORef
import qualified System.Timeout
import Data.Maybe
import Data.Functor
import qualified Data.Traversable as Trav

import Agda.Utils.Permutation (permute, takeP)
import Agda.TypeChecking.Monad hiding (withCurrentModule)
-- import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Monad.MetaVars
-- import Agda.TypeChecking.Monad.Context
-- import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty (prettyA)
import qualified Text.PrettyPrint as PP
import qualified Agda.TypeChecking.Pretty as TCM
import Agda.Syntax.Position
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcreteEnv, abstractToConcrete_, makeEnv, runAbsToCon, toConcrete)
import Agda.Interaction.BasicOps hiding (refine)
import Agda.TypeChecking.Reduce (normalise)
import Agda.Syntax.Common
import qualified Agda.Syntax.Scope.Base as Scope
import Agda.Syntax.Scope.Monad (withCurrentModule)
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.TypeChecking.Monad.Base as TCM
import Agda.TypeChecking.EtaContract (etaContract)
import qualified Agda.Utils.HashMap as HMap

import Agda.Auto.Convert
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl
import Agda.Auto.Typecheck

import Agda.Auto.CaseSplit

import Agda.Utils.Except ( runExceptT, MonadError(catchError) )
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Tuple

#include "undefined.h"

insertAbsurdPattern :: String -> String
insertAbsurdPattern [] = []
insertAbsurdPattern s@(_:_) | take (length abspatvarname) s == abspatvarname = "()" ++ drop (length abspatvarname) s
insertAbsurdPattern (c:s) = c : insertAbsurdPattern s

getName :: A.Expr -> Maybe (Bool, I.QName)
getName (A.ScopedExpr _ e) = getName e
getName (A.Def qname) = Just (False, qname)
getName (A.Proj _ qname) = Just (False, head $ I.unAmbQ qname)
getName (A.Con qname) = Just (True, head $ I.unAmbQ qname)
getName _ = Nothing

dispmsg :: String ->
           TCM (Either [(InteractionId, String)]
                       (Either [String] String)
               , Maybe String)
dispmsg msg = return (Left [], Just msg)

-- | Entry point for Auto tactic (Agsy).
--
--     @auto ii rng s = return (res, mmsg)@
--
--   If @mmsg = Just msg@, the message @msg@ produced by Agsy should
--   be displayed to the user.
--
--   The result @res@ of the Auto tactic can be one of the following three:
--
--   1. @Left [(ii,s)]@
--      A list of solutions @s@ for interaction ids @ii@.
--      In particular, @Left []@ means Agsy found no solution.
--
--   2. @Right (Left cs)@
--      A list of clauses (the user allowed case-split).
--
--   3. @Right (Right s)@
--      A refinement for the interaction id @ii@ in which Auto was invoked.

auto
  :: InteractionId
  -> Range
  -> String
  -> TCM ( Either [(InteractionId, String)]
                  (Either [String] String)
         , Maybe String)
auto ii rng argstr = do

  -- Parse hints and other configuration.
  let (hints, timeout, pick, mode, hintmode) = parseargs argstr
  ahints <- case mode of
    MRefine{} -> return []
    _         -> mapM (parseExprIn ii rng) hints
  let failHints = dispmsg "Hints must be a list of constant names"
  caseMaybe (mapM getName ahints) failHints $ \ ehints -> do

    -- Get names for equality reasoning.
    -- @eqstuff == []@ if any of these names is not defined.
    eqstuffExprs <- mapM (parseExprIn ii rng) ["_≡_", "begin_", "_≡⟨_⟩_", "_∎", "sym", "cong"]
      `catchError`
        (\_ -> return [])
    let eqstuff = fromMaybe [] $ mapM getName eqstuffExprs

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
               trms <- runExceptT $ mapM (\ (m, _, _, _) -> frommy (Meta m)) $ Map.elems tccons
               case trms of
                 Left{}     -> writeIORef nsol $! nsol' + 1
                 Right trms -> modifyIORef sols (trms :)
                 -- Right trms -> if listmode then modifyIORef sols (trms :)
                 --                           else writeIORef sols [trms]
        ticks <- liftIO $ newIORef 0

        let exsearch initprop recinfo defdfv =
             liftIO $ System.Timeout.timeout (timeout * 1000000) $ loop 0
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

        let getsols sol = do
             exprs <- forM (zip (Map.keys tccons) sol) $ \ (mi, e) -> do
               mv   <- lookupMeta mi
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
                    mytype' = foldl (\x y -> NotM $ Pi Nothing Agda.Auto.Syntax.NotHidden (freeIn 0 y) y (Abs NoId x)) mytype restargs
                    htyp = negtype ee mytype'
                    sctx = (Id "h", closify htyp) : map (\x -> (NoId, closify x)) modargs
                    ntt = closify (NotM $ App Nothing (NotM OKVal) (Const ee) (NotM ALNil))
                res <- exsearch (tcSearchSC False sctx ntt (Meta m)) Nothing defdfv
                rsols <- liftM reverse $ liftIO $ readIORef sols
                if null rsols then do
                  nsol' <- liftIO $ readIORef nsol
                  dispmsg $ insuffsols (pick + numsols - nsol')
                 else do
                  aexprss <- mapM getsols rsols
                  cexprss <- forM aexprss $ mapM $ \(mi, e) -> do
                    mv <- lookupMeta mi
                    withMetaInfo (getMetaInfo mv) $ do
                      (mi,) <$> abstractToConcrete_ e
                  let ss = dropWhile (== ' ') . dropWhile (/= ' ') . show
                      disp [(_, cexpr)] = ss cexpr
                      disp cexprs = concat $ map (\ (mi, cexpr) -> ss cexpr ++ " ") cexprs
                  ticks <- liftIO $ readIORef ticks
                  dispmsg $ unlines $
                    ("Listing disproof(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1)) :
                    for (zip cexprss [pick..]) (\ (x, y) -> show y ++ "  " ++ disp x)
            _ -> dispmsg "Metavariable dependencies not allowed in disprove mode"
           _ -> dispmsg "Metavariable dependencies not allowed in disprove mode"
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
          let timeoutString | isNothing res = " after timeout (" ++ show timeout ++ "s)"
                            | otherwise     = ""
          if listmode then do
            rsols <- liftM reverse $ liftIO $ readIORef sols
            if null rsols then do
              nsol' <- liftIO $ readIORef nsol
              dispmsg $ insuffsols (pick + numsols - nsol') ++ timeoutString
             else do
              aexprss <- mapM getsols rsols
              -- cexprss <- mapM (mapM (\(mi, e) -> lookupMeta mi >>= \mv -> withMetaInfo (getMetaInfo mv) $ abstractToConcrete_ e >>= \e' -> return (mi, e'))) aexprss
              cexprss <- forM aexprss $ do
                mapM $ \ (mi, e) -> do
                  mv <- lookupMeta mi
                  withMetaInfo (getMetaInfo mv) $ do
                    e' <- abstractToConcrete_ e
                    return (mi, e')
              let disp [(_, cexpr)] = show cexpr
                  disp cexprs = concat $ for cexprs $ \ (mi, cexpr) ->
                    maybe (show mi) show (lookup mi riis)
                      ++ " := " ++ show cexpr ++ " "
              ticks <- liftIO $ readIORef ticks
              dispmsg $ "Listing solution(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ timeoutString ++
                        "\n" ++ unlines (map (\(x, y) -> show y ++ "  " ++ disp x) $ zip cexprss [pick..])
           else {- not listmode -}
            case res of
             Nothing -> do
              nsol' <- liftIO $ readIORef nsol
              dispmsg $ insuffsols (pick + numsols - nsol') ++ timeoutString
             Just depthreached -> do
              ticks <- liftIO $ readIORef ticks
              rsols <- liftIO $ readIORef sols
              case rsols of
                [] -> do
                  nsol' <- liftIO $ readIORef nsol
                  dispmsg $ insuffsols (pick + numsols - nsol')
                terms -> loop terms where
                  -- Andreas, 2015-05-17  Issue 1504
                  -- If giving a solution failed (e.g. ill-typed)
                  -- we could try the next one.
                  -- However, currently @terms@ is always a singleton list.
                  -- Thus, the following @loop@ is not doing something very
                  -- meaningful.
                  loop [] = return (Left [], Just "")
                  loop (term : terms') = do
                    -- On exception, try next solution
                    flip catchError (const $ loop terms') $ do
                      exprs <- getsols term
                      reportSDoc "auto" 20 $ TCM.text "Trying solution " TCM.<+> TCM.prettyTCM exprs
                      giveress <- forM exprs $ \ (mi, expr0) -> do
                        let expr = killRange expr0
                        case lookup mi riis of
                         Nothing ->
                          -- catchError
                           (giveExpr mi expr >> return (Nothing, Nothing))
                           -- (const retry)
                           -- (\_ -> return (Nothing, Just ("Failed to give expr for side solution of " ++ show mi)))
                         Just ii' -> do ae <- give ii' Nothing expr
                                        mv <- lookupMeta mi
                                        let scope = getMetaScope mv
                                        ce <- abstractToConcreteEnv (makeEnv scope) ae
                                        let cmnt = if ii' == ii then agsyinfo ticks else ""
                                        return (Just (ii', show ce ++ cmnt), Nothing)
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
                          msg' = case msgs of
                                  [] -> Nothing
                                  _ -> Just $ unlines msgs
                      return (Left $ catMaybes $ map fst giveress, msg')

     MCaseSplit -> do
      case thisdefinfo of
       Just (def, clause, True) ->
        case Map.elems tccons of
         [(m, mytype, mylocalVars, _)] | null eqcons -> do
          (ids, pats) <- constructPats cmap mi clause
          let ctx = map (\((hid, id), t) -> HI hid (id, t)) (zip ids mylocalVars)
          ticks <- liftIO $ newIORef 0
          let [rectyp'] = mymrectyp
          defdfv <- getdfv mi def
          myrecdef <- liftIO $ newIORef $ ConstDef {cdname = "", cdorigin = (Nothing, def), cdtype = rectyp', cdcont = Postulate, cddeffreevars = defdfv}
          sols <- liftIO $ System.Timeout.timeout (timeout * 1000000) (
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
             Left{} -> dispmsg "No solution found"
             Right cls' -> do
              cls'' <- forM cls' $ \ (I.Clause _ tel ps body t catchall) -> do
                withCurrentModule (AN.qnameModule def) $ do
                 -- Normalise the dot patterns
                 ps <- addContext tel $ normalise ps
                 body <- etaContract body
                 liftM modifyAbstractClause $ inTopContext $ reify $ AN.QNamed def $ I.Clause noRange tel ps body t catchall
              pcs <- withInteractionId ii $ mapM prettyA cls''
              ticks <- liftIO $ readIORef ticks


              return (Right $ Left (map (insertAbsurdPattern . PP.renderStyle (PP.style { PP.mode = PP.OneLineMode })) pcs), Nothing)

           Just [] -> dispmsg "No solution found" -- case not possible at the moment because case split doesnt care about search exhaustiveness
           Nothing -> dispmsg $ "No solution found at time out (" ++ show timeout ++ "s)"
         _ -> dispmsg "Metavariable dependencies not allowed in case split mode"
       _ -> dispmsg "Metavariable is not at top level of clause RHS"

     MRefine listmode -> do
      mv <- lookupMeta mi
      let tt = jMetaType $ mvJudgement mv
          minfo = getMetaInfo mv
      targettyp <- withMetaInfo minfo $ do
       vs <- getContextArgs
       targettype <- tt `piApplyM` permute (takeP (length vs) $ mvPermutation mv) vs
       normalise targettype
      let tctx = length $ envContext $ clEnv minfo

      hits <- if elem "-a" hints then do
        st <- liftTCM $ join $ pureTCM $ \st _ -> return st
        let defs = st^.stSignature.sigDefinitions
            idefs = st^.stImports.sigDefinitions
            alldefs = HMap.keys defs ++ HMap.keys idefs
        liftM catMaybes $ mapM (\n ->
          case thisdefinfo of
           Just (def, _, _) | def == n -> return Nothing
           _ -> do
            cn <- withMetaInfo minfo $ runAbsToCon $ toConcrete n
            if head (show cn) == '.' then -- not in scope
              return Nothing
             else do
              c <- getConstInfo n
              ctyp <- normalise $ defType c
              cdfv <- withMetaInfo minfo $ getDefFreeVars n
              return $ case matchType cdfv tctx ctyp targettyp of
               Nothing -> Nothing
               Just score -> Just (show cn, score)
         ) alldefs
       else do
        let scopeinfo = clScope (getMetaInfo mv)
            namespace = Scope.everythingInScope scopeinfo
            names = Scope.nsNames namespace
            qnames = map (\(x, y) -> (x, Scope.anameName $ head y)) $ Map.toList names
            modnames = case thisdefinfo of
                        Just (def, _, _) -> filter (\(_, n) -> n /= def) qnames
                        Nothing -> qnames
        liftM catMaybes $ mapM (\(cn, n) -> do
          c <- getConstInfo n
          ctyp <- normalise $ defType c
          cdfv <- withMetaInfo minfo $ getDefFreeVars n
          return $ case matchType cdfv tctx ctyp targettyp of
           Nothing -> Nothing
           Just score -> Just (show cn, score)
         ) modnames

      let sorthits = sortBy (\(_, (pa1, pb1)) (_, (pa2, pb2)) -> case compare pa2 pa1 of {EQ -> compare pb1 pb2; o -> o}) hits
      if listmode || pick == (-1) then
        let pick' = max 0 pick
        in if pick' >= length sorthits then
             dispmsg $ insuffcands $ length sorthits
            else
             let showhits = take 10 $ drop pick' sorthits
             in dispmsg $ "Listing candidate(s) " ++ show pick' ++ "-" ++ show (pick' + length showhits - 1) ++ " (found " ++ show (length sorthits) ++ " in total)\n" ++
                           unlines (map (\(i, (cn, _)) -> show i ++ "  " ++ cn) (zip [pick'..pick' + length showhits - 1] showhits))
       else
        if pick >= length sorthits then
         dispmsg $ insuffcands $ length sorthits
        else
         return (Right $ Right (fst $ sorthits !! pick), Nothing)
  where
    agsyinfo ticks = ""

-- Get the functions and axioms defined in the same module as @def@.
autohints :: AutoHintMode -> I.MetaId -> Maybe AN.QName ->
             TCM [(Bool, AN.QName)]
autohints AHMModule mi (Just def) = do
  scope <- clScope . getMetaInfo <$> lookupMeta mi
  let names     = Scope.nsNames $ Scope.everythingInScope scope
      qnames    = map (Scope.anameName . head) $ Map.elems names
      modnames  = filter (\n -> AN.qnameModule n == AN.qnameModule def && n /= def) qnames
  map (False,) <$> do
    (`filterM` modnames) $ \ n -> do
      c <- getConstInfo n
      case theDef c of
        Axiom{}    -> return True
        AbstractDefn{} -> return True
        Function{} -> return True
        _          -> return False

autohints _ _ _ = return []

insuffsols :: Int -> String
insuffsols 0 = "No solution found"
insuffsols n = "Only " ++ show n ++ " solution(s) found"

insuffcands :: Int -> String
insuffcands 0 = "No candidate found"
insuffcands n = "Only " ++ show n ++ " candidate(s) found"

data Mode = MNormal Bool Bool -- true if list mode, true if disprove

          | MCaseSplit

          | MRefine Bool -- true if list mode


data AutoHintMode = AHMNone
                  | AHMModule

parseargs :: String -> ([String], Int, Int, Mode, AutoHintMode)
parseargs s =
 let r ("-t" : timeout : ws) (_, pick, mode, hintmode) =
      r ws (read timeout, pick, mode, hintmode)
     r ("-s" : pick : ws) (timeout, _, mode, hintmode) =
      r ws (timeout, read pick, mode, hintmode)


     r ("-l" : ws) (timeout, pick, MNormal _ disprove, hintmode) =
      r ws (timeout, pick, MNormal True disprove, hintmode)
     r ("-l" : ws) (timeout, pick, MRefine _, hintmode) =
      r ws (timeout, pick, MRefine True, hintmode)
     r ("-d" : ws) (timeout, pick, MNormal listmode _, hintmode) =
      r ws (timeout, pick, MNormal listmode True, hintmode)
     r ("-m" : ws) (timeout, pick, mode, _) =
      r ws (timeout, pick, mode, AHMModule)

     r ("-c" : ws) (timeout, pick, _, hintmode) =
      r ws (timeout, pick, MCaseSplit, hintmode)

     r ("-r" : ws) (timeout, pick, _, hintmode) =
      r ws (timeout, (-1), MRefine False, hintmode)
     r (h : ws) x =
      let (hints, timeout, pick, mode, hintmode) = r ws x
      in (h : hints, timeout, pick, mode, hintmode)
     r [] (x,y,z,w) = ([],x,y,z,w)
 in r (words s) (5, 0, MNormal False False, AHMNone)
