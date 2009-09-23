{-# LANGUAGE UndecidableInstances#-}

module Agda.Auto.Auto (auto) where

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
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete, abstractToConcrete_, makeEnv)
import Agda.Interaction.Monad
import Agda.Interaction.BasicOps hiding (refine)
import Agda.Utils.Monad.Undo

import Agda.Auto.Convert
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.Typecheck
import Agda.Auto.Print


getName :: A.Expr -> Maybe (Bool, I.QName)
getName (A.ScopedExpr _ e) = getName e
getName (A.Def qname) = Just (False, qname)
getName (A.Con qname) = Just (True, head $ I.unAmbQ qname)
getName _ = Nothing

dispmsg msg = return ([], Just msg)

auto :: InteractionId -> Range -> String -> TCM ([(InteractionId, String)], Maybe String)
auto ii rng argstr = liftTCM $  
     do  let (hints, timeout, pick, mode) = parseargs argstr
         ahints <- mapM (parseExprIn ii rng) hints
         case mapM getName ahints of
          Nothing -> dispmsg "Hints must be a list of constant names" 
          Just ehints -> do
           mi <- lookupInteractionId ii
           (myhints, tccons, eqcons, cmap) <- tomy mi ehints
           let (mainm, _, _, _) = tccons Map.! mi
           case mode of
            MNormal listmode -> do
             sols <- liftIO $ newIORef []
             nsol <- liftIO $ newIORef (if listmode then (pick + 10) else (pick + 1))
             let hsol = if listmode then do
                         nsol' <- readIORef nsol
                         when (nsol' <= 10) $ mapM (\(m, _, _, _) -> frommy (Meta m)) (Map.elems tccons) >>= \trms -> modifyIORef sols (trms :)
                        else do
                         nsol' <- readIORef nsol
                         when (nsol' == 1) $ mapM (\(m, _, _, _) -> frommy (Meta m)) (Map.elems tccons) >>= \trms -> writeIORef sols [trms]
             ticks <- liftIO $ newIORef 0
             res <- liftIO $ System.Timeout.timeout (timeout * 1000000) $
              let r d =
                   do
                    let tc (m, mytype, mylocalVars) isdep = tcExp isdep (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) (Meta m)
                        initprop = foldl (\x (ineq, e, i) -> mpret $ And Nothing x (comp ineq (closify e) (closify i)))
                                    (foldl (\x (m, mt, mlv, _) -> mpret $ And Nothing x (tc (m, mt, mlv) (not $ hequalMetavar m mainm)))
                                     (mpret OK)
                                     (Map.elems tccons)
                                    )
                                    eqcons
                    depreached <- topSearch ticks nsol hsol undefined False (RIEnv myhints) (initprop) d 1
                    nsol' <- readIORef nsol
                    if nsol' /= 0 && depreached then
                      r (d + 1)
                     else
                      return depreached
              in  r 0
             let getsols sol = do
                  exprs <- mapM (\(mi, e) -> do
                             mv <- lookupMeta mi
                             expr <- withMetaInfo (getMetaInfo mv) $ reify e
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
                      Just ii' -> do (ae, []) <- give ii' Nothing expr  -- `catchError` (\_ -> throwError (strMsg $ "Solution is not accepted by Agda: " ++ show term))
                                     mv <- lookupMeta mi
                                     let scope = getMetaScope mv
                                         ce = abstractToConcrete (makeEnv scope) ae
                                     let cmnt = if ii' == ii then " {- by agsy" ++ (if null argstr then "" else " (" ++ argstr ++ ")") ++ " -}" else ""
                                     return $ Just (ii', show ce ++ cmnt)
                                    
                     ) exprs
                   let msg = if length exprs == 1 then
                              Nothing
                             else
                              Just $ "Also gave solution(s) for hole(s)" ++
                                      concatMap (\(mi', _) ->
                                       if mi' == mi then "" else (" " ++ case lookup mi' riis of {Nothing -> show mi'; Just ii -> show ii})
                                      ) exprs
                   return (catMaybes giveress, msg)
            MDumpProblem (Just dumpfile) -> do
             tcconss <- mapM (\(m, mytype, mylocalVars, _) -> do
               let typ = foldl (\x y -> NotM $ Pi Agda.Auto.Syntax.NotHidden undefined y (Abs NoId x)) mytype mylocalVars
                   trm = foldl (\x _ -> NotM $ Lam Agda.Auto.Syntax.NotHidden (Abs NoId x)) (Meta m) mylocalVars
               typs <- liftIO $ printExp [] typ
               trms <- liftIO $ printExp [] trm
               return $ (if hequalMetavar m mainm then "the_prob : " else "extra_con : ") ++ typs ++ " {\n = " ++ trms ++ ";\n};\n\n"
              ) (Map.elems tccons)
             constss <- liftIO $ mapM (\(_, (TMAll, c)) -> printConst c >>= \s -> return $ s ++ "\n") (Map.toList cmap)
             eqconss <- liftIO $ mapM (\(ineq, e1, e2) -> do
                         pe1 <- printExp [] e1
                         pe2 <- printExp [] e2
                         return $ "-- " ++ pe1 ++ (if ineq then " >= " else " == ") ++ pe2
                        ) eqcons
             let probs = concat constss ++ concat tcconss ++ (if null ehints then "" else ("-- hints: " ++ concatMap (\(_, n) -> " " ++ show n) ehints) ++ "\n") ++
                         "-- " ++ show (length eqcons) ++ " eqcons\n" ++ unlines eqconss
             liftIO $ writeFile dumpfile probs
             dispmsg $ "Dumping problem to " ++ dumpfile
            MDumpProblem Nothing -> do
             mv <- lookupMeta mi
             let HasType _ tt = mvJudgement mv
                 minfo = getMetaInfo mv
                 localVars = map (snd . unArg . ctxEntry) . envContext . clEnv $ minfo
             withMetaInfo minfo $ do
              vs <- getContextArgs
              let targettype = tt `piApply` vs
              targettype <- rewrite Normalised targettype
              localVars <- mapM (rewrite Normalised) localVars
              dispmsg $ "Target type: " ++ show (localVars, targettype)

insuffsols 0 = "No solution found"
insuffsols n = "Only " ++ show n ++ " solution(s) were found"

data Mode = MNormal Bool  -- true if list mode
          | MDumpProblem (Maybe String)  -- Just filename to dump as agsy file or Nothing to show the problem in internal agda format

parseargs s =
 let r ("-t" : timeout : ws) (_, pick, mode) =
      r ws (read timeout, pick, mode)
     r ("-s" : pick : ws) (timeout, _, mode) =
      r ws (timeout, read pick, mode)
     r ("-dump" : dumpfile : ws) (timeout, pick, _) =
      r ws (timeout, pick, MDumpProblem (Just dumpfile))
     r ("-dumpa" : ws) (timeout, pick, _) =
      r ws (timeout, pick, MDumpProblem Nothing)
     r ("-l" : ws) (timeout, pick, _) =
      r ws (timeout, pick, MNormal True)
     r (h : ws) x =
      let (hints, timeout, pick, mode) = r ws x
      in  (h : hints, timeout, pick, mode)
     r [] (x,y,z) = ([],x,y,z)
 in  r (words s) (1, 0, MNormal False)


