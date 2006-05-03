{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as List

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute

#include "../../undefined.h"

isDecl ce = case ce of Decl _ _ _    -> True; _ -> False
isDefn ce = case ce of Defn _ _      -> True; _ -> False
isNmsp ce = case ce of NameSpace _ _ -> True; _ -> False

-- | add a declaration to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a v = local ((Decl x a Nothing :) . adjust 1) v
    

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
    ctx <- ask
    case (filter isDecl ctx) !! n of
        Decl _ a _ -> return a
	_	   -> __IMPOSSIBLE__

-- | get either type or definition of a constant. 
--   this navigates namespace structure and uses passed
--     function to find data after right namespace is reached
--
getConstInfoM :: (Signature -> Name -> a) -> QName -> TCM a
getConstInfoM fun c = do
    ctx <- ask  -- need to look here for local definitions
    sig <- gets sigSt 
    return $ getConstInfo fun (ctx++sig) c

getConstInfo :: (Signature -> Name -> a) -> Context -> QName -> a
getConstInfo = error "use abstract names here"
-- getConstInfo fun ctx (Qual pkg name) = 
--     case List.find (\ (NameSpace x _) -> x == pkg) (filter isNmsp ctx) of
--         Just (NameSpace _ ctx') -> getConstInfo fun ctx' name
-- getConstInfo fun ctx (QName c) = fun ctx c

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst = getConstInfoM find where
    find sig c = case List.find (\ (Decl x _ _) -> x == c) (filter isDecl sig) of
        Just (Decl _ a _) -> a
	_		  -> __IMPOSSIBLE__



