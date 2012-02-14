{-# LANGUAGE CPP #-}

-- | Change constructors and cases on builtins and natish datatypes to use
--   primitive data
module Agda.Compiler.Epic.Primitive where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Internal(QName)
import qualified Agda.Syntax.Internal as T
import Agda.TypeChecking.Monad hiding (defName)
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.Monad (andM)

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface
import Agda.Compiler.Epic.NatDetection

#include "../../undefined.h"
import Agda.Utils.Impossible

{- Stacken, Heapen -- Optimizern -}

data PrimTransform = PrimTF
  { mapCon        :: Map QName Var
  , translateCase :: Expr -> [Branch] -> Expr
  }

prZero, prSuc, prTrue, prFalse, prPred, prNatEquality :: Var
prZero  = "primZero"
prSuc   = "primSuc"
prTrue  = "primTrue"
prFalse = "primFalse"
prPred  = "primPred"
prNatEquality = "primNatEquality"

-- | Change constructors and cases on builtins and natish datatypes to use
--   primitive data
primitivise :: [Fun] -> Compile TCM [Fun]
primitivise funs = do
    ptfs   <- getBuiltins
    natish <- getNatish
    mapM (primFun $ ptfs ++ map (uncurry natPrimTF) natish) funs

-- | Map primitive constructors to primitive tags
initialPrims :: Compile TCM () -- [Fun]
initialPrims = do
  -- TODO: Natishness is calculated here and could be stored so it does not have
  --       to be recalculated in primitivise
  natish <- getNatish
  -- This has to be done because injection detection may otherwise flag injections
  -- between non-primitive and primitive datatypes in the wrong way
  sequence_ [zipWithM_ putConstrTag [zc, sc] (prim [prZero, prSuc])
            | (_, [zc, sc]) <- natish]
  sequence_
    [ [builtinNil, builtinCons]           ~> tags [0, 1]
    , [builtinZero, builtinSuc  ]         ~> prim [prZero, prSuc]
    , [builtinLevelZero, builtinLevelSuc] ~> prim [prZero, prSuc]
    , [builtinTrue, builtinFalse]         ~> prim [prTrue, prFalse]
    , [builtinRefl]                       ~> tags [0]
    ]
  where
    prim = map PrimTag
    tags = map Tag
    constrs ~> tags = do
        builtins  <- lift $ mapM getBuiltin' constrs
        if all isJust builtins
           then do
                let names = map (defName . fromMaybe __IMPOSSIBLE__) builtins
                -- b <- and <$>  mapM constrInScope names
                -- if b then return $ Just (transf names) else return Nothing
                zipWithM_ putConstrTag names tags
           else return ()

-- | Build transforms using the names of builtins
getBuiltins :: Compile TCM [PrimTransform]
getBuiltins =
    catMaybes <$> sequence
      [ [builtinZero, builtinSuc  ]         ~> natPrimTF [NotForced]
       -- ? is this ok to have [NotForced]
      , [builtinLevelZero, builtinLevelSuc] ~> natPrimTF [NotForced]
      , [builtinTrue, builtinFalse]         ~> boolPrimTF
      ]
  where
    constrs ~> transf = do
        builtins  <- lift $ mapM getBuiltin' constrs
        if all isJust builtins
           then do
                let names = map (defName . fromMaybe __IMPOSSIBLE__) builtins
                b <- andM $ map constrInScope names
                if b then return $ Just (transf names) else return Nothing
           else return Nothing

defName (T.Def q []) = q
defName (T.Con q []) = q
defName _            = __IMPOSSIBLE__

head'' (x:xs) e = x
head'' _      e = e

-- | Translation to primitive integer functions
natPrimTF :: ForcedArgs -> [QName] -> PrimTransform
natPrimTF filt [zero, suc] = PrimTF
  { mapCon = M.fromList [(zero, prZero), (suc, prSuc)]
  , translateCase = \ce brs -> case brs of
        -- Assuming only the first two branches are relevant when casing on Nats
        (Branch _ n vs e:Branch _ _n' vs'' e'':_) ->
            if n == zero
               then primNatCaseZS ce e  (head'' vs'' __IMPOSSIBLE__) e''
               else primNatCaseZS ce e'' (head'' vs __IMPOSSIBLE__) e
        (Branch _ n vs e:Default e'':_) ->
            if n == zero
               then primNatCaseZD ce e e'' -- zero
               else primNatCaseZS ce e'' (head'' vs __IMPOSSIBLE__) e -- suc
        [ Branch _ n vs e ] ->
            if n == zero
              then e
              else lett (head'' vs __IMPOSSIBLE__) (App prPred [ce]) e
        _ -> __IMPOSSIBLE__
  }
natPrimTF _ _ = __IMPOSSIBLE__

-- | Corresponds to a case for natural numbers
primNatCaseZS :: Expr -- ^ Expression that is cased on
              -> Expr -- ^ Expression for the zero branch
              -> Var  -- ^ Variable that is bound in suc branch
              -> Expr -- ^ Expression used for suc branch
              -> Expr -- ^ Result?
primNatCaseZS n zeroBr v sucBr =
    If (App prNatEquality [n, Var prZero]) zeroBr (lett v (App prPred [n]) sucBr)

-- | Corresponds to a case with a zero and default branch
primNatCaseZD :: Expr -- ^ Expression that is cased on
              -> Expr -- ^ Zero branch
              -> Expr -- ^ Default branch
              -> Expr -- ^ Result?
primNatCaseZD n zeroBr defBr = If (App prNatEquality [n, Var prZero]) zeroBr defBr

-- | Translation to primitive bool functions
boolPrimTF :: [QName] -> PrimTransform
boolPrimTF [true, false] = PrimTF
  { mapCon = M.fromList [(true, prTrue), (false, prFalse)]
  , translateCase = \ce brs ->
    case brs of
        (Branch _ n _vs e:b':_) ->
                    (if n == true
                             then If ce e (brExpr b')
                             else If ce (brExpr b') e)
        _ -> __IMPOSSIBLE__
  }
boolPrimTF _ = __IMPOSSIBLE__

-- | Change all the primitives in the function using the PrimTransform
primFun :: [PrimTransform] -> Fun -> Compile TCM Fun
primFun ptfs (Fun i n qn c args e) =
    Fun i n qn c args <$> primExpr ptfs e
primFun _ e@(EpicFun {}) = return e


-- | Change all the primitives in an expression using PrimTransform
primExpr :: [PrimTransform] -> Expr -> Compile TCM Expr
primExpr prim ex = case ex of
    Var{}    -> return ex
    Lit{}    -> return ex
    Lam v e1 -> Lam v <$> primExpr prim e1
    Con c n es -> case testCon prim n of
        Just pn -> do
            filt <- getForcedArgs n
            apps pn <$> mapM (primExpr prim) es
        Nothing -> Con c n <$> mapM (primExpr prim) es
    App v es   -> App v <$> mapM (primExpr prim) es
    Case e brs -> case testBranch prim brs of
       Just p  -> primExpr prim $ translateCase p e brs
       Nothing -> Case <$> primExpr prim e <*> mapM primBranch brs
    If a b c   -> If <$> primExpr prim a <*> primExpr prim b <*> primExpr prim c
    Let v e e' -> Let v <$> primExpr prim e <*> primExpr prim e'
    Lazy e     -> Lazy <$> primExpr prim e
    UNIT       -> return ex
    IMPOSSIBLE -> return ex
  where
    -- | Test if any PrimTransform have any primitive function for
    --   a constructor, gives the name of that primitive function in that
    --   case, otherwise Nothing.
    testCon :: [PrimTransform] -> QName -> Maybe Var
    testCon [] _ = Nothing
    testCon (p : ps) k = M.lookup k (mapCon p) `mplus` testCon ps k

    -- | Test if we should transform the case, based on the branches. Returns
    --   the (first) PrimTransform that is applicable.
    testBranch :: [PrimTransform] -> [Branch] -> Maybe PrimTransform
    testBranch [] _       = Nothing
    testBranch (p:ps) brs = msum (map (check p) brs) `mplus` testBranch ps brs

    -- | Check if a particular PrimTransform can be used on a particular Branch
    --   Returns the PrimTransform in that case.
    check :: PrimTransform -> Branch -> Maybe PrimTransform
    check p br = case br of
        Branch  _ n _ _ -> fmap (const p) $ M.lookup n (mapCon p)
        BrInt _ _       -> Nothing
        Default _       -> Nothing

    -- | Change all primitives in a branch
    primBranch :: Branch -> Compile TCM Branch
    primBranch br = do
        e' <- primExpr prim (brExpr br)
        return br {brExpr = e'}
