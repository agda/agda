

{-# LANGUAGE UndecidableInstances#-}

module Agda.Auto.Auto (auto) where

import Agda.Utils.Impossible
-- mode: Agda implicit arguments
-- mode: Omitted arguments, used for implicit constructor type arguments
-- mode: A sort can be unknown, used as a hack for Agda's universe polymorphism
import Control.Monad.Error
import Control.Monad.State
import System.IO.Unsafe (unsafePerformIO)
import Data.List
import Data.Generics
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IORef
import qualified System.Timeout
import Data.Maybe (catMaybes)
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
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete, abstractToConcrete_, makeEnv)
import Agda.Interaction.Monad
import Agda.Interaction.BasicOps hiding (refine)
import Agda.Interaction.MakeCase (findClause)
import Agda.TypeChecking.Reduce (normalise)
import Agda.Syntax.Scope.Monad (withCurrentModule)
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.TypeChecking.Monad.Base as MB
import Agda.TypeChecking.EtaContract (etaContract)
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

auto :: InteractionId -> Range -> String -> TCM (Either [(InteractionId, String)] [String], Maybe String)
auto ii rng argstr = liftTCM $ do
         let (hints, timeout, pick, mode) = parseargs argstr
         ahints <- mapM (parseExprIn ii rng) hints
         case mapM getName ahints of
          Nothing -> dispmsg "Hints must be a list of constant names"
          Just ehints -> do
           mi <- lookupInteractionId ii
           (myhints, tccons, eqcons, cmap) <- tomy mi ehints
           let (mainm, _, _, _) = tccons Map.! mi
           case mode of
            MNormal listmode disprove -> do
               sols <- liftIO $ newIORef []
               nsol <- liftIO $ newIORef (if listmode then (pick + 10) else (pick + 1))
               let hsol recinfo =
                       let getterm trm = case recinfo of
                                          Nothing -> return trm
                                          Just (_, _, recdef, recvar) -> expandExp trm >>= \trm -> return $ renamec recvar recdef trm
                       in if listmode then do
                           nsol' <- readIORef nsol
                           when (nsol' <= 10) $ mapM (\(m, _, _, _) -> getterm (Meta m) >>= frommy) (Map.elems tccons) >>= \trms -> modifyIORef sols (trms :)
                          else do
                           nsol' <- readIORef nsol
                           when (nsol' == 1) $ mapM (\(m, _, _, _) -> getterm (Meta m) >>= frommy) (Map.elems tccons) >>= \trms -> writeIORef sols [trms]
               ticks <- liftIO $ newIORef 0
               let exsearch initprop recinfo = liftIO $ System.Timeout.timeout (timeout * 1000000) (
                    let r d = do
                         depreached <- topSearch ticks nsol (hsol recinfo) (RIEnv myhints) (initprop) d costIncrease
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
                       let mytype' = foldl (\x y -> NotM $ Pi Nothing Agda.Auto.Syntax.NotHidden (freeIn 0 y) y (Abs NoId x)) mytype mylocalVars
                           htyp = negtype mytype'
                       res <- exsearch (tcSearch False [(Id "h", closify htyp), (NoId, closify (NotM $ Sort (Set 0)))] (closify (NotM $ App Nothing (NotM OKVal) (Var 1) (NotM ALNil))) (Meta m)) Nothing
                       rsols <- liftM reverse $ liftIO $ readIORef sols
                       if null rsols then do
                         nsol' <- liftIO $ readIORef nsol
                         dispmsg $ insuffsols (pick + (if listmode then 10 else 1) - nsol')
                        else do
                         aexprss <- mapM getsols rsols
                         cexprss <- mapM (mapM (\(mi, e) -> lookupMeta mi >>= \mv -> withMetaInfo (getMetaInfo mv) $ abstractToConcrete_ e >>= \e' -> return (mi, e'))) aexprss
                         let disp [(_, cexpr)] = show cexpr
                             disp cexprs = concat (map (\(mi, cexpr) -> show cexpr ++ " ") cexprs)
                         dispmsg $ "Listing disproof(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ "\n" ++
                                           unlines (map (\(x, y) -> show y ++ "  " ++ disp x) $ zip cexprss [pick..])
                   _ -> dispmsg "Metavariable dependencies not allowed in disprove mode"
                  _ -> dispmsg "Metavariable dependencies not allowed in disprove mode"
                else do
                 recinfo <- do
                  res <- catchError (findClause mi >>= \x -> return (Just x)) (\_ -> return Nothing)
                  case res of
                   Just (def, clause) -> do
                    recdef <- getConstInfo def
                    let rectyp = MB.defType recdef
                    rectyp <- normalise rectyp
                    (rectyp', _) <- runStateT (tomyType rectyp) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing})
                    myrecdef <- liftIO $ newIORef $ ConstDef {cdname = "", cdorigin = (Nothing, def), cdtype = rectyp', cdcont = Postulate}
                    (_, pats) <- constructPats cmap clause
                    let recvar = let [(_, _, mlv, _)] = filter (\(m, _, _, _) -> hequalMetavar m mainm) (Map.elems tccons)
                                 in length mlv
                    return $ Just (rectyp', pats, myrecdef, recvar)
                   Nothing -> return Nothing
                 let tc (m, mytype, mylocalVars) isdep = tcSearch isdep (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) (Meta m)
                     initprop =
                       foldl (\x (ineq, e, i) -> mpret $ And Nothing x (comp' ineq (closify e) (closify i)))
                        (foldl (\x (m, mt, mlv, _) ->
                          if hequalMetavar m mainm then
                           case recinfo of
                            Just (rectype, recpats, _, _) ->
                             mpret $ Sidecondition (localTerminationSidecond (localTerminationEnv recpats) (length mlv) (Meta m))
                                                   (tc (m, mt, mlv ++ [rectype]) False)
                            Nothing -> mpret $ And Nothing x (tc (m, mt, mlv) False)
                          else
                           mpret $ And Nothing x (tc (m, mt, mlv) True)
                         )
                         (mpret OK)
                         (Map.elems tccons)
                        ) eqcons
                 res <- exsearch initprop recinfo
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
                     dispmsg $ "Listing solution(s) " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ "\n" ++
                                       unlines (map (\(x, y) -> show y ++ "  " ++ disp x) $ zip cexprss [pick..])
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
                                         let cmnt = if ii' == ii then agsyinfo else ""
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
             res <- catchError (findClause mi >>= \x -> return (Just x)) (\_ -> return Nothing)
             case res of
              Just (def, clause) ->
               case Map.elems tccons of
                ((m, mytype, mylocalVars, _) : []) | null eqcons -> do





                 (ids, pats) <- constructPats cmap clause
                 let pids = concat $ map (\(_, x) -> " " ++ case x of {Id s -> s; NoId -> "noid"}) ids
                     ctx = map (\((hid, id), t) -> HI hid (id, t)) (zip ids mylocalVars)
                 ticks <- liftIO $ newIORef 0

                 recdef <- getConstInfo def
                 let rectyp = MB.defType recdef
                 rectyp <- normalise rectyp
                 (rectyp', _) <- runStateT (tomyType rectyp) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing})
                 myrecdef <- liftIO $ newIORef $ ConstDef {cdname = "", cdorigin = (Nothing, def), cdtype = rectyp', cdcont = Postulate}
                 sols <- liftIO $ System.Timeout.timeout (timeout * 1000000) (
                    let r d = do
                         sols <- liftIO $ caseSplitSearch ticks (throwImpossible (Impossible ("agsy: " ++ "Auto.hs") 243)) myhints (throwImpossible (Impossible ("agsy: " ++ "Auto.hs") 243)) d myrecdef ctx mytype pats
                         case sols of
                          [] -> r (d + costIncrease)
                          (_:_) -> return sols
                    in r 0)
                 case sols of
                  Just (cls : _) -> do
                   cls' <- liftIO $ mapM frommyClause cls
                   cls'' <- mapM (\(I.Clause _ tel perm ps body) ->
                     withCurrentModule (AN.qnameModule def) $ do
                      -- Normalise the dot patterns
                      ps <- addCtxTel tel $ normalise ps
                      body <- etaContractBody body
                      liftM modifyAbstractClause $ inContext [] $ reify $ NamedClause def $ I.Clause noRange tel perm ps body
                    ) cls'
                   pcs <- withInteractionId ii $ mapM prettyA cls''
                   return (Right (map (insertAbsurdPattern . PP.renderStyle (PP.style { PP.mode = PP.OneLineMode })) pcs ++ [agsyinfo]), Nothing)
                  Just [] -> dispmsg "No solution found" -- case not possible at the moment because case split doesnt care about search exhaustiveness
                  Nothing -> dispmsg $ "No solution found at time out (" ++ show timeout ++ "s)"
                _ -> dispmsg "Metavariable dependencies not allowed in case split mode"
              Nothing -> dispmsg "Metavariable is not at top level of clause RHS"
 where
  agsyinfo = " {- by agsy" ++ (if null argstr then "" else " (" ++ argstr ++ ")") ++ " -}"
insuffsols 0 = "No solution found"
insuffsols n = "Only " ++ show n ++ " solution(s) found"
data Mode = MNormal Bool Bool -- true if list mode, true if disprove
          | MCaseSplit
parseargs s =
 let r ("-t" : timeout : ws) (_, pick, mode) =
      r ws (read timeout, pick, mode)
     r ("-s" : pick : ws) (timeout, _, mode) =
      r ws (timeout, read pick, mode)
     r ("-l" : ws) (timeout, pick, MNormal _ disprove) =
      r ws (timeout, pick, MNormal True disprove)
     r ("-d" : ws) (timeout, pick, MNormal listmode _) =
      r ws (timeout, pick, MNormal listmode True)
     r ("-c" : ws) (timeout, pick, _) =
      r ws (timeout, pick, MCaseSplit)
     r (h : ws) x =
      let (hints, timeout, pick, mode) = r ws x
      in (h : hints, timeout, pick, mode)
     r [] (x,y,z) = ([],x,y,z)
 in r (words s) (5, 0, MNormal False False)
