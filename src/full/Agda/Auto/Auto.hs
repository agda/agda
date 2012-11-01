{-# LANGUAGE CPP #-}

module Agda.Auto.Auto (auto) where

import Agda.Utils.Impossible
#include "../undefined.h"

import Control.Monad.Error
import Control.Monad.State
import System.IO.Unsafe (unsafePerformIO)
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IORef
import qualified System.Timeout
import Data.Maybe (catMaybes)

import Agda.Utils.Permutation (permute, takeP)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Substitute
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty (prettyA)
import qualified Text.PrettyPrint as PP
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete, abstractToConcrete_, makeEnv, runAbsToCon, toConcrete)
import Agda.Interaction.BasicOps hiding (refine)
import Agda.Interaction.MakeCase (findClause)
import Agda.TypeChecking.Reduce (normalise)
import qualified Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (withCurrentModule)
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.TypeChecking.Monad.Base as MB
import Agda.TypeChecking.EtaContract (etaContract)
import qualified Agda.Utils.HashMap as HMap

import Agda.Auto.Convert
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl
import Agda.Auto.Typecheck


import Agda.Auto.CaseSplit


insertAbsurdPattern [] = []
insertAbsurdPattern s@(_:_) | take (length abspatvarname) s == abspatvarname = "()" ++ drop (length abspatvarname) s
insertAbsurdPattern (c:s) = c : insertAbsurdPattern s

getName :: A.Expr -> Maybe (Bool, I.QName)
getName (A.ScopedExpr _ e) = getName e
getName (A.Def qname) = Just (False, qname)
getName (A.Con qname) = Just (True, head $ I.unAmbQ qname)
getName _ = Nothing

dispmsg msg = return (Left [], Just msg)

auto :: InteractionId -> Range -> String -> TCM (Either [(InteractionId, String)] (Either [String] String), Maybe String)
auto ii rng argstr = liftTCM $ do
         let (hints, timeout, pick, mode, hintmode) = parseargs argstr
         ahints <- mapM (parseExprIn ii rng) (case mode of {MRefine{} -> []; _ -> hints})

         eqstuff <- liftM (maybe Nothing (mapM getName)) $
                    catchError (liftM Just $ mapM (parseExprIn ii rng) ["_≡_", "begin_", "_≡⟨_⟩_", "_∎", "sym", "cong"]) (\_ -> return Nothing)

         case mapM getName ahints of
          Nothing -> dispmsg "Hints must be a list of constant names"
          Just ehints -> do
           mi <- lookupInteractionId ii
           --thisdefinfo <- catchError (liftM Just $ findClause mi) (\_ -> return Nothing)
           thisdefinfo <- findClauseDeep mi
           ehints <- liftM (ehints ++) $ autohints hintmode mi (case thisdefinfo of {Just (def, _, _) -> Just def; Nothing -> Nothing})
           mrectyp <- case thisdefinfo of
            Nothing -> return []
            Just (def, _, _) -> do
             recdef <- getConstInfo def
             let rectyp = MB.defType recdef
             rectyp <- normalise rectyp
             return [rectyp]

           let ehints' = ehints ++ maybe [] id eqstuff


           (myhints', mymrectyp, tccons, eqcons, cmap) <- tomy mi ehints' mrectyp

           let myhints = take (length myhints' - (length ehints' - length ehints)) myhints'
               meqr = case eqstuff of
                       Nothing -> Nothing
                       Just _ -> let [c1, c2, c3, c4, c5, c6] = drop (length myhints' - (length ehints' - length ehints)) myhints'
                                 in Just $ EqReasoningConsts c1 c2 c3 c4 c5 c6


           let tcSearchSC isdep ctx typ trm =

                                     (case meqr of
                                      Nothing -> id
                                      Just eqr -> mpret . Sidecondition (calcEqRState eqr trm)
                                     )

                                     (tcSearch isdep ctx typ trm)
           let (mainm, _, _, _) = tccons Map.! mi
           case mode of
            MNormal listmode disprove -> do
               sols <- liftIO $ newIORef ([] :: [[I.Term]])
               nsol <- liftIO $ newIORef (if listmode then (pick + 10) else (pick + 1))
               let hsol =


                       if listmode then do
                        nsol' <- readIORef nsol
                        when (nsol' <= 10) $ runErrorT (mapM (\(m, _, _, _) -> frommy (Meta m)) (Map.elems tccons)) >>= \trms -> case trms of {Left{} -> writeIORef nsol $! nsol' + 1; Right trms -> modifyIORef sols (trms :)}
                       else do
                        nsol' <- readIORef nsol
                        when (nsol' == 1) $ runErrorT (mapM (\(m, _, _, _) -> frommy (Meta m)) (Map.elems tccons)) >>= \trms -> case trms of {Left{} -> writeIORef nsol $! nsol' + 1; Right trms -> writeIORef sols [trms]}
               ticks <- liftIO $ newIORef 0
               let exsearch initprop recinfo defdfv = liftIO $ System.Timeout.timeout (timeout * 1000000) (
                    let r d = do
                         let rechint x = case recinfo of
                                          Nothing -> x
                                          Just (_, recdef) -> (recdef, HMRecCall) : x
                             env = RIEnv {rieHints = rechint $ map (\x -> (x, HMNormal)) myhints,
                                          rieDefFreeVars = defdfv

                                          , rieEqReasoningConsts = meqr

                                         }
                         depreached <- topSearch ticks nsol hsol env (initprop) d costIncrease
                         nsol' <- readIORef nsol
                         if nsol' /= 0 && depreached then
                           r (d + costIncrease)
                          else
                           return depreached
                    in r 0)
               let getsols sol = do
                    exprs <- mapM (\(mi, e) -> do
                               mv <- lookupMeta mi
                               e <- etaContract e
                               expr <- liftM modifyAbstractExpr $ withMetaInfo (getMetaInfo mv) $ reify e
                               return (mi, expr)
                              ) (zip (Map.keys tccons) sol)
                    let r :: I.MetaId -> StateT [I.MetaId] TCM [(I.MetaId, A.Expr)]
                        r midx = do
                         let (m, _, _, deps) = tccons Map.! midx
                         asolss <- mapM r deps
                         dones <- get
                         asols <- if (midx `notElem` dones) then do
                           put (midx : dones)
                           return [(midx, let Just e = lookup midx exprs in e)]
                          else
                           return []
                         return $ concat asolss ++ asols
                    (asols, _) <- runStateT (r mi) []
                    return asols
               if disprove then
                 case eqcons of
                  [] -> case Map.elems tccons of
                   (m, mytype, mylocalVars, _) : [] -> do
                       defdfv <- case thisdefinfo of
                                  Just (def, _, _) -> getdfv mi def
                                  Nothing -> return 0
                       ee <- liftIO $ newIORef $ ConstDef {cdname = "T", cdorigin = __IMPOSSIBLE__, cdtype = NotM $ Sort (Set 0), cdcont = Postulate, cddeffreevars = 0}
                       let modargs = drop (length mylocalVars - defdfv) mylocalVars
                           restargs = take (length mylocalVars - defdfv) mylocalVars
                           mytype' = foldl (\x y -> NotM $ Pi Nothing Agda.Auto.Syntax.NotHidden (freeIn 0 y) y (Abs NoId x)) mytype restargs
                           htyp = negtype ee mytype'
                           sctx = (Id "h", closify htyp) : map (\x -> (NoId, closify x)) modargs
                           ntt = closify (NotM $ App Nothing (NotM OKVal) (Const ee) (NotM ALNil))
                       res <- exsearch (tcSearchSC False sctx ntt (Meta m)) Nothing defdfv
                       rsols <- liftM reverse $ liftIO $ readIORef sols
                       if null rsols then do
                         nsol' <- liftIO $ readIORef nsol
                         dispmsg $ insuffsols (pick + (if listmode then 10 else 1) - nsol')
                        else do
                         aexprss <- mapM getsols rsols
                         cexprss <- mapM (mapM (\(mi, e) -> lookupMeta mi >>= \mv -> withMetaInfo (getMetaInfo mv) $ abstractToConcrete_ e >>= \e' -> return (mi, e'))) aexprss
                         let ss = dropWhile (== ' ') . dropWhile (/= ' ') . show
                             disp [(_, cexpr)] = ss cexpr
                             disp cexprs = concat (map (\(mi, cexpr) -> ss cexpr ++ " ") cexprs)
                         ticks <- liftIO $ readIORef ticks
                         dispmsg $ "Listing disproof(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++


                                   "\n" ++ unlines (map (\(x, y) -> show y ++ "  " ++ disp x) $ zip cexprss [pick..])
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
                 iis <- getInteractionPoints
                 riis <- mapM (\ii -> lookupInteractionId ii >>= \mi -> return (mi, ii)) iis
                 if listmode then do
                   rsols <- liftM reverse $ liftIO $ readIORef sols
                   if null rsols then do
                     nsol' <- liftIO $ readIORef nsol
                     dispmsg $ insuffsols (pick + 10 - nsol')
                    else do
                     aexprss <- mapM getsols rsols
                     cexprss <- mapM (mapM (\(mi, e) -> lookupMeta mi >>= \mv -> withMetaInfo (getMetaInfo mv) $ abstractToConcrete_ e >>= \e' -> return (mi, e'))) aexprss
                     let disp [(_, cexpr)] = show cexpr
                         disp cexprs = concat (map (\(mi, cexpr) -> case lookup mi riis of {Nothing -> show mi; Just ii -> show ii} ++ " := " ++ show cexpr ++ " ") cexprs)
                     ticks <- liftIO $ readIORef ticks
                     dispmsg $ "Listing solution(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++


                               "\n" ++ unlines (map (\(x, y) -> show y ++ "  " ++ disp x) $ zip cexprss [pick..])
                  else
                   case res of
                    Nothing -> do
                     nsol' <- liftIO $ readIORef nsol
                     dispmsg $ insuffsols (pick + 1 - nsol') ++ " at time out (" ++ show timeout ++ "s)"
                    Just depthreached -> do
                     ticks <- liftIO $ readIORef ticks
                     rsols <- liftIO $ readIORef sols
                     case rsols of
                      [] -> do
                       nsol' <- liftIO $ readIORef nsol
                       dispmsg $ insuffsols (pick + 1 - nsol')
                      (term : _) -> do
                       exprs <- getsols term
                       giveress <-
                        mapM (\(mi, expr) ->
                         case lookup mi riis of
                          Nothing -> giveExpr mi expr >>= \_ -> return Nothing
                          Just ii' -> do (ae, []) <- give ii' Nothing expr
                                         mv <- lookupMeta mi
                                         let scope = getMetaScope mv
                                             ce = abstractToConcrete (makeEnv scope) ae
                                         let cmnt = if ii' == ii then agsyinfo ticks else ""
                                         return $ Just (ii', show ce ++ cmnt)
                         ) exprs
                       let msg = if length exprs == 1 then
                                  Nothing
                                 else
                                  Just $ "Also gave solution(s) for hole(s)" ++
                                          concatMap (\(mi', _) ->
                                           if mi' == mi then "" else (" " ++ case lookup mi' riis of {Nothing -> show mi'; Just ii -> show ii})
                                          ) exprs
                       return (Left $ catMaybes giveress, msg)

            MCaseSplit -> do
             case thisdefinfo of
              Just (def, clause, True) ->
               case Map.elems tccons of
                ((m, mytype, mylocalVars, _) : []) | null eqcons -> do


                 (ids, pats) <- constructPats cmap mi clause
                 let pids = concat $ map (\(_, x) -> " " ++ case x of {Id s -> s; NoId -> "noid"}) ids
                     ctx = map (\((hid, id), t) -> HI hid (id, t)) (zip ids mylocalVars)
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
                   cls' <- liftIO $ runErrorT (mapM frommyClause cls)
                   case cls' of
                    Left{} -> dispmsg "No solution found"
                    Right cls' -> do
                     cls'' <- mapM (\(I.Clause _ tel perm ps body) ->
                       withCurrentModule (AN.qnameModule def) $ do
                        -- Normalise the dot patterns
                        ps <- addCtxTel tel $ normalise ps
                        body <- etaContractBody body
                        liftM modifyAbstractClause $ inContext [] $ reify $ AN.QNamed def $ I.Clause noRange tel perm ps body
                      ) cls'
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
              let targettype = tt `piApply` permute (takeP (length vs) $ mvPermutation mv) vs
              normalise targettype
             let tctx = length $ envContext $ clEnv minfo

             hits <- if elem "-a" hints then do
               st <- liftTCM $ join $ pureTCM $ \st _ -> return st
               let defs = sigDefinitions $ stSignature st
                   idefs = sigDefinitions $ stImports st
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
                   namespace = Agda.Syntax.Scope.Base.everythingInScope scopeinfo
                   names = Agda.Syntax.Scope.Base.nsNames namespace
                   qnames = map (\(x, y) -> (x, Agda.Syntax.Scope.Base.anameName $ head y)) $ Map.toList names
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
autohints AHMModule mi (Just def) = do
 mv <- lookupMeta mi
 let scopeinfo = clScope (getMetaInfo mv)
     namespace = Agda.Syntax.Scope.Base.everythingInScope scopeinfo
     names = Agda.Syntax.Scope.Base.nsNames namespace
     qnames = map (Agda.Syntax.Scope.Base.anameName . head) $ Map.elems names
     modnames = filter (\n -> AN.qnameModule n == AN.qnameModule def && n /= def) qnames
 modnames' <- filterM (\n -> do
   c <- getConstInfo n
   return (case theDef c of
            Axiom{} -> True
            Function{} -> True
            _ -> False
          )
  ) modnames
 return $ map (\x -> (False, x)) modnames'
autohints _ _ _ = return []

insuffsols 0 = "No solution found"
insuffsols n = "Only " ++ show n ++ " solution(s) found"

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
