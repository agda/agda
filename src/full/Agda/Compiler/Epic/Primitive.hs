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

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.NatDetection

#include "../../undefined.h"
import Agda.Utils.Impossible

{- Stacken, Heapen -- Optimizern -}

data PrimTransform = PrimTF
  { mapCon        :: Map QName Var
  , translateCase :: Expr -> [Branch] -> Expr
  }

-- | Change constructors and cases on builtins and natish datatypes to use
--   primitive data
primitivise :: MonadTCM m => [Fun] -> Compile m [Fun]
primitivise funs = do
    ptfs   <- getBuiltins
    natish <- getNatish
    lists  <- primLists
    (++ lists) <$> mapM (primFun $ ptfs ++ map (uncurry natPrimTF) natish) funs

-- | Create primitive functions if list constructors are marked as builtins
primLists :: MonadTCM m => Compile m [Fun]
primLists = do
    mnil  <- lift $ getBuiltin' builtinNil
    mcons <- lift $ getBuiltin' builtinCons
    case (mnil, mcons) of
      (Just (T.Con nil []), Just (T.Con cons [])) -> do
          [nilT, consT] <- mapM getConstrTag [nil, cons]
          let fun s n = Fun
                   { funInline  = True
                   , funName    = "prim" ++ s
                   , funComment = "BUILTIN " ++ s
                   , funArgs    = []
                   , funExpr    = Var (unqname n)
                   }
          return [ fun "Nil" nil
                 , fun "Cons" cons
                 , Fun
                    { funInline  = False
                    , funName    = "primListElim"
                    , funComment = "Eliminator for Lists"
                    , funArgs    = ["op" , "z" , "xs"]
                    , funExpr    = Case (Var "xs")
                        [ Branch nilT nil [] $ Var "z"
                        , Branch consT cons ["y", "ys"] $
                            App "op" [ Var "y"
                                     , App "primListElim" [ Var "op"
                                                          , Var "z"
                                                          , Var "ys"
                                                          ]
                                     ]
                        ]
                    }
                 ]
      _                     -> return []
-- | Build transforms using the names of builtins
getBuiltins :: MonadTCM m => Compile m [PrimTransform]
getBuiltins =
    catMaybes <$> sequence
      [ [builtinZero, builtinSuc  ]         ~> natPrimTF [True]
       -- ? is this ok to have [True]
      , [builtinLevelZero, builtinLevelSuc] ~> natPrimTF [True]
      , [builtinTrue, builtinFalse]         ~> boolPrimTF
      ]
  where
    constrs ~> transf = do
        builtins <- lift $ mapM getBuiltin' constrs
        if all isJust builtins
           then return $ Just (transf (map (defName . fromMaybe __IMPOSSIBLE__) builtins))
           else return Nothing
    defName (T.Def q []) = q
    defName (T.Con q []) = q
    defName _            = __IMPOSSIBLE__

-- | Translation to primitive integer functions
natPrimTF :: IrrFilter -> [QName] -> PrimTransform
natPrimTF filt [zero, suc] = PrimTF
  { mapCon = M.fromList [(zero, "primZero"), (suc, "primSuc")]
  , translateCase = \ce brs -> case brs of
        -- Assuming only the first two branches are relevant when casing on Nats
        (Branch _ n vs e:Branch _ _n' vs' e':_) ->
            if n == zero
               then primNatCaseZS ce e  (head (pairwiseFilter filt vs')) e'
               else primNatCaseZS ce e' (head (pairwiseFilter filt vs )) e
        (Branch _ n vs e:Default e':_) ->
            if n == zero
               then primNatCaseZD ce e e' -- zero
               else primNatCaseZS ce e' (head (pairwiseFilter filt vs )) e -- suc
        [ Branch _ n vs e ] ->
            if n == zero
              then e
              else Let (head (pairwiseFilter filt vs)) (App "primPred" [ce]) e
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
    If (App "primNatEquality" [n, Var "primZero"]) zeroBr (Let v (App "primPred" [n]) sucBr)

-- | Corresponds to a case with a zero and default branch
primNatCaseZD :: Expr -- ^ Expression that is cased on
              -> Expr -- ^ Zero branch
              -> Expr -- ^ Default branch
              -> Expr -- ^ Result?
primNatCaseZD n zeroBr defBr = If (App "primNatEquality" [n, Var "primZero"]) zeroBr defBr

-- | Translation to primitive bool functions
boolPrimTF :: [QName] -> PrimTransform
boolPrimTF [true, false] = PrimTF
  { mapCon = M.fromList [(true, "primTrue"), (false, "primFalse")]
  , translateCase = \ce brs ->
    case brs of
        [Branch _ n _vs e, b'] ->
                    (if n == true
                             then If ce e (brExpr b')
                             else If ce (brExpr b') e)
        _ -> __IMPOSSIBLE__
  }
boolPrimTF _ = __IMPOSSIBLE__

-- | Change all the primitives in the function using the PrimTransform
primFun :: MonadTCM m => [PrimTransform] -> Fun -> Compile m Fun
primFun ptfs (Fun i n c args e) =
    Fun i n c args <$> primExpr ptfs e
primFun _ e@(EpicFun {}) = return e


-- | Change all the primitives in an expression using PrimTransform
primExpr :: MonadTCM m => [PrimTransform] -> Expr -> Compile m Expr
primExpr prim ex = case ex of
    Var{}    -> return ex
    Lit{}    -> return ex
    Lam v e1 -> Lam v <$> primExpr prim e1
    Con c n es -> case testCon prim n of
        Just pn -> do
            filt <- getIrrFilter n
            apps pn <$> mapM (primExpr prim) (pairwiseFilter filt es)
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
    primBranch :: MonadTCM m => Branch -> Compile m Branch
    primBranch br = do
        e' <- primExpr prim (brExpr br)
        return br {brExpr = e'}
