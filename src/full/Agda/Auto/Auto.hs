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

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Substitute
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Position
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete, makeEnv)
import Agda.Interaction.Monad
import Agda.Interaction.BasicOps hiding (refine)
import Agda.Utils.Monad.Undo

import Agda.Auto.Convert
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.Typecheck
import Agda.Auto.Print


getName :: A.Expr -> (Bool, I.QName)
getName (A.ScopedExpr _ e) = getName e
getName (A.Def qname) = (False, qname)
getName (A.Con qname) = (True, head $ I.unAmbQ qname)
getName _ = error "getName: no match"

auto :: InteractionId -> Range -> String -> TCM (Either (A.Expr,[InteractionId]) String)
auto ii rng argstr = liftTCM $  
     do  let (hints, timeout, pick, mode) = parseargs argstr
         ahints <- mapM (parseExprIn ii rng) hints
         let ehints = map getName ahints
         mi <- lookupInteractionId ii

         (mainm, myhints, tccons, eqcons, cmap) <- tomy mi ehints
         case mode of
          MNormal listmode -> do
           sols <- liftIO $ newIORef []
           nsol <- liftIO $ newIORef (if listmode then (pick + 10) else (pick + 1))
           let hsol = if listmode then do
                       nsol' <- readIORef nsol
                       when (nsol' <= 10) $ frommy (Meta mainm) >>= \trm' -> modifyIORef sols (trm' :)
                      else do
                       nsol' <- readIORef nsol
                       when (nsol' == 1) $ frommy (Meta mainm) >>= \trm' -> writeIORef sols [trm']
               hpartsol = error "no hpartsol"
           ticks <- liftIO $ newIORef 0
{-
           liftIO $ putStrLn $ show (length extras) ++ " extras"
           liftIO $ mapM_ (\(m, ts) ->
                     do putStrLn (show (length ts))
                        ts' <- mapM (printExp []) ts
                        mapM_ putStrLn ts'
                        putStrLn ""
                    ) extras
-}
           depthreached <- liftIO $ System.Timeout.timeout (timeout * 1000000) $
            let r d =
                 do
                  let tc (m, mytype, mylocalVars) isdep = tcExp isdep (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) (Meta m)
                      initprop = foldl (\x (ineq, e, i) -> mpret $ And Nothing x (comp ineq (closify e) (closify i)))
                                  (foldl (\x tcc@(m, _, _) -> mpret $ And Nothing x (tc tcc (not $ hequalMetavar m mainm)))
                                   (mpret OK)
                                   tccons
                                  )
                                  eqcons
                  depreached <- topSearch ticks nsol hsol hpartsol False (RIEnv myhints) (initprop) d 1
                  nsol' <- readIORef nsol
                  if nsol' /= 0 && depreached then
                    r (d + 1)
                   else
                    return depreached
            in  r 0
           mv <- lookupMeta mi
           withMetaInfo (getMetaInfo mv) $ do
            if listmode then do
              rsols <- liftIO $ readIORef sols
              if null rsols then do
                nsol' <- liftIO $ readIORef nsol
                return $ Right $ "Only " ++ show (pick + 10 - nsol') ++ " solutions were found"
               else do
                aexprs <- mapM reify $ reverse rsols
                scope <- getInteractionScope ii
                let cexprs = map (abstractToConcrete (makeEnv scope)) aexprs
                return $ Right $ "Listing solutions " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ "\n" ++
                                  unlines (map (\(x, y) -> show y ++ "  " ++ x) $ zip (map show cexprs) [pick..])
             else
              case depthreached of
               Nothing -> do
                nsol' <- liftIO $ readIORef nsol
                return $ Right $ "Timeout (" ++ show (pick + 1 - nsol') ++ " solutions found)"
               Just depthreached -> do
                ticks <- liftIO $ readIORef ticks
                rsols <- liftIO $ readIORef sols
                case rsols of
                 [] -> do
                  nsol' <- liftIO $ readIORef nsol
                  if nsol' == pick + 1 then
                    return $ Right "No solution found"
                   else
                    return $ Right $ "Only " ++ show (pick + 1 - nsol') ++ " solutions were found"
                 (term : _) -> do
                  expr <- reify term
                  liftM Left $ give ii Nothing expr `catchError` (\_ -> throwError (strMsg $ "Solution is not accepted: " ++ show term))
          MDumpProblem (Just dumpfile) -> do
           tcconss <- mapM (\(m, mytype, mylocalVars) -> do
             let typ = foldl (\x y -> NotM $ Pi Agda.Auto.Syntax.NotHidden y (Abs NoId x)) mytype mylocalVars
                 trm = foldl (\x _ -> NotM $ Lam Agda.Auto.Syntax.NotHidden (Abs NoId x)) (Meta m) mylocalVars
             typs <- liftIO $ printExp [] typ
             trms <- liftIO $ printExp [] trm
             return $ (if hequalMetavar m mainm then "the_prob : " else "extra_con : ") ++ typs ++ "\n = " ++ trms ++ "\n\n"
            ) tccons
           constss <- liftIO $ mapM (\(_, (TMAll, c)) -> printConst c >>= \s -> return $ s ++ "\n") (Map.toList cmap)
           let probs = concat constss ++ concat tcconss ++ (if null ehints then "" else ("-- hints: " ++ concatMap (\(_, n) -> " " ++ show n) ehints) ++ "\n") ++
                       show (length eqcons) ++ " eqcons\n"
           liftIO $ writeFile dumpfile probs
           return $ Right $ "Dumping problem to " ++ dumpfile
          MDumpProblem Nothing -> do
           mv <- lookupMeta mi
           let HasType _ tt = mvJudgement mv
               minfo = getMetaInfo mv
               localVars = map (snd . unArg . ctxEntry) . envContext . clEnv $ minfo
           withMetaInfo minfo $ do  -- this is needed for rewrite or getContextArgs to get in right context
            vs <- getContextArgs
            let targettype = tt `piApply` vs
            targettype <- rewrite Normalised targettype
            localVars <- mapM (rewrite Normalised) localVars
            return $ Right $ "Target type: " ++ show (localVars, targettype)
         
{-
         mv <- lookupMeta mi
         let HasType _ tt = mvJudgement mv
             minfo = getMetaInfo mv
             localVars = map (snd . unArg . ctxEntry) . envContext . clEnv $ minfo
         withMetaInfo minfo $ do  -- this is needed for rewrite or getContextArgs to get in right context
          vs <- getContextArgs
          let targettype = tt `piApply` vs
          targettype <- rewrite Normalised targettype
          localVars <- mapM (rewrite Normalised) localVars
          case mode of
           MDumpProblem Nothing ->
            return $ Right $ "Target type: " ++ show targettype
           _ -> do
            ((mytype : mylocalVars, myhints), extras, cmap) <- tomy (targettype : localVars, ehints)
            m <- liftIO $ Agda.Auto.NarrowingSearch.newMeta Nothing
            let mytrm = Meta m
            case mode of
             MNormal listmode -> do
              sols <- liftIO $ newIORef []
              nsol <- liftIO $ newIORef (if listmode then (pick + 10) else (pick + 1))
              let hsol = if listmode then do
                          nsol' <- readIORef nsol
                          when (nsol' <= 10) $ frommy mytrm >>= \trm' -> modifyIORef sols (trm' :)
                         else do
                          nsol' <- readIORef nsol
                          when (nsol' == 1) $ frommy mytrm >>= \trm' -> writeIORef sols [trm']
                  hpartsol = error "no hpartsol"  -- printExp [] mytrm >>= \trms -> putStrLn ("sol: " ++ trms)
              ticks <- liftIO $ newIORef 0
              depthreached <- liftIO $ System.Timeout.timeout (timeout * 1000000) $
               let r d =
                    do
                     let initprop = foldl (\x (m, mytype : mylocalVars) -> mpret $ And Nothing x (tcExp True (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) (Meta m)))
                                     (tcSearch (map (\x -> (NoId, closify x)) mylocalVars) (closify mytype) mytrm)
                                     extras
                     depreached <- topSearch ticks nsol hsol hpartsol False (RIEnv myhints) (initprop) d 1
                     nsol' <- readIORef nsol
                     if nsol' /= 0 && depreached then
                       r (d + 1)
                      else
                       return depreached
               in  r 0
              if listmode then do
                rsols <- liftIO $ readIORef sols
                if null rsols then do
                  nsol' <- liftIO $ readIORef nsol
                  return $ Right $ "Only " ++ show (pick + 10 - nsol') ++ " solutions were found"
                 else do
                  aexprs <- mapM reify $ reverse rsols
                  scope <- getInteractionScope ii
                  let cexprs = map (abstractToConcrete (makeEnv scope)) aexprs
                  return $ Right $ "Listing solutions " ++ show pick ++ "-" ++ show (pick + length rsols - 1) ++ "\n" ++
                                    unlines (map (\(x, y) -> show y ++ "  " ++ x) $ zip (map show cexprs) [pick..])
               else
                case depthreached of
                 Nothing -> do
                  nsol' <- liftIO $ readIORef nsol
                  return $ Right $ "Timeout (" ++ show (pick + 1 - nsol') ++ " solutions found)"
                 Just depthreached -> do
                  ticks <- liftIO $ readIORef ticks
                  rsols <- liftIO $ readIORef sols
                  case rsols of
                   [] -> do
                    nsol' <- liftIO $ readIORef nsol
                    if nsol' == pick + 1 then
                      return $ Right "No solution found"
                     else
                      return $ Right $ "Only " ++ show (pick + 1 - nsol') ++ " solutions were found"
                   (term : _) -> do
                    expr <- reify term
                    liftM Left $ give ii Nothing expr `catchError` (\_ -> throwError (strMsg $ "Solution is not accepted: " ++ show term))
             MDumpProblem (Just dumpfile) -> do
              let typ = foldl (\x y -> NotM $ Pi Agda.Auto.Syntax.NotHidden y (Abs NoId x)) mytype mylocalVars
                  trm = foldl (\x _ -> NotM $ Lam Agda.Auto.Syntax.NotHidden (Abs NoId x)) mytrm mylocalVars
              typs <- liftIO $ printExp [] typ
              trms <- liftIO $ printExp [] trm
              let theprobs = "the_prob : " ++ typs ++ "\n = " ++ trms
              constss <- liftIO $ mapM (\(_, (TMAll, c)) -> printConst c >>= \s -> return $ s ++ "\n") (Map.toList cmap)
              let probs = concat constss ++ theprobs ++ (if null ehints then "" else "  -- -h" ++ concatMap (\(_, n) -> " " ++ show n) ehints) ++ "\n"
              liftIO $ writeFile dumpfile probs
              return $ Right $ "Dumping problem to " ++ dumpfile
             _ -> error "happens not"
-}

data Mode = MNormal Bool  -- is list mode
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


