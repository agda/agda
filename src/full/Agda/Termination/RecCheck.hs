{-# LANGUAGE CPP #-}

{- Checking for recursion:

   - We detect truly (co)recursive definitions by computing the
     dependency graph and checking for cycles.

   - This is inexpensive and let us skip the termination check 
     when there's no (co)recursion
   
   The traversal over the definitions is taken from Agda.Termination.TermCheck, 
   but simplified since here we don't care about the arguments of the calls.

-}

module Agda.Termination.RecCheck
    ( recursive )
 where

import Control.Monad.Error
import Control.Applicative

import Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import Data.Monoid

import Data.Graph

import Agda.Syntax.Internal as I
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (instantiate, instantiateFull)
import Agda.TypeChecking.Level (reallyUnLevelView)

import Agda.Utils.Monad ((<$>), mapM', forM', ifM, or2M)


#include "../undefined.h"
import Agda.Utils.Impossible

recursive :: [QName] -> TCM Bool
recursive names = do
   graph <- map (\(n,ns) -> (n,nub ns)) . zip names <$> mapM (recDef names) names
   reportSLn "rec.graph" 20 $ show graph
   return $ cyclic graph

cyclic :: [(QName, [QName])] -> Bool
cyclic g = not . null $ [() | CyclicSCC _ <- stronglyConnComp (map (\(n,ns) -> ((),n,ns)) g)]

recDef :: [QName] -> QName -> TCM [QName]
recDef names name = do
	-- Retrieve definition
        def <- getConstInfo name

        case theDef def of
          Function{ funClauses = cls } -> mapM' (rekClause names) cls
          _                            -> return mempty


rekClause :: [QName] -> Clause -> TCM [QName]
rekClause names
    (Clause { clauseTel  = tel
            , clausePerm = perm
            , clausePats = argPats'
            , clauseBody = body }) = do
    case clause2Term body of
       Nothing -> return mempty
       Just t  -> recTerm names t
  where
    clause2Term :: ClauseBody -> Maybe Term
    clause2Term (Body t)           = Just t
    clause2Term (Bind (Abs _ b))   = clause2Term b
    clause2Term (Bind (NoAbs _ b)) = clause2Term b
    clause2Term NoBody             = Nothing

recTerm :: [QName] -> Term -> TCM [QName]
recTerm names t0 = do
  loop t0
  where

       loopSort :: Sort -> TCM [QName]
       loopSort s = do

         case s of
           Type (Max [])              -> return mempty
           Type (Max [ClosedLevel _]) -> return mempty
           Type t -> loop (Level t)
           Prop   -> return mempty
           Inf    -> return mempty
           DLub s1 (NoAbs x s2) -> mappend <$> loopSort s1 <*> loopSort s2
           DLub s1 (Abs x s2)   -> mappend <$> loopSort s1 <*> loopSort s2

       loopType :: Type -> TCM [QName]
       loopType (El s t) = mappend <$> loopSort s <*> loop t

       loop
         :: Term          -- ^ Part of function body from which calls are to be extracted.
         -> TCM [QName]
       loop t = do
         case ignoreSharing t of
            Con c args        -> mapM' (loop . unArg) args
            Def g args        -> mappend [g |  g `elem` names] <$> mapM' (loop . unArg) args
            Lam h (Abs x t)   -> loop t
            Lam h (NoAbs _ t) -> loop t
            Var i args        -> mapM' loop (map unArg args)
            Pi a (Abs x b)    -> mappend <$> loopType (unDom a) <*> loopType b
            Pi a (NoAbs _ b)  -> mappend <$> loopType (unDom a) <*> loopType b
            Lit l             -> return mempty
            Sort s            -> loopSort s
            MetaV x args      -> loopMeta x args
            DontCare t        -> loop t
            Level l           -> do
              l <- catchError (reallyUnLevelView l) $ const $ internalError $
                "Termination checker: cannot view level expression, " ++
                "probably due to missing level built-ins."
              loop l

            Shared{} -> __IMPOSSIBLE__

       loopMeta x args = do
         reportSLn "rec.mvar" 10 $ "RecChecking mvar: " ++ show x
         mi <- mvInstantiation <$> lookupMeta x
         case mi of
           InstV a -> mapM' loop (a : map unArg args)
           -- Unsolved metas are not considered termination problems, there
           -- will be a warning for them anyway.
           _       -> return mempty

