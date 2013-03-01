{-# LANGUAGE CPP #-}
-- | Some arguments to functions (types in particular) will not be used in the
--   body. Wouldn't it be useful if these wasn't passed around at all?
--   Fear not, we here perform some analysis and try to remove as many of these
--   occurences as possible.
--
--   We employ the worker/wrapper transform, so if f x1 .. xn = e
--   and we notice that some is not needed we create: f' xj .. xk = e [xi := unit]
--   and f x1 .. xn = f' xj .. xk.
--   i.e we erase them in f' and replace by unit, and the original f function
--   calls the new f'. The idea is that f should be inlined and then peace on earth.
module Agda.Compiler.Epic.Erasure where

import Control.Applicative
import Control.Monad.State
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface

import Agda.TypeChecking.Monad.Base (TCM)
import qualified Agda.Syntax.Internal as SI
import qualified Agda.Syntax.Common   as SC
import Agda.TypeChecking.Monad (MonadTCM, reportSDoc)
import Agda.TypeChecking.Pretty as P

#include "../../undefined.h"
import Agda.Utils.Impossible

isIrr :: Relevance -> Bool
isIrr Irr      = True
isIrr Rel      = False

isRel :: Relevance -> Bool
isRel = not . isIrr

-- | Relevance "or"
(||-) :: Relevance -> Relevance -> Relevance
Irr      ||- b      = b
_        ||- _      = Rel
infixr 2 ||-

-- | Relevance "and"
(&&-) :: Relevance -> Relevance -> Relevance
Rel      &&- b      = b
_        &&- _      = Irr
infixr 3 &&-

data ErasureState = ErasureState
  { relevancies :: Map Var [Relevance]
  , funs        :: Map Var Fun
  }

type Erasure = StateT ErasureState

-- | Try to find as many unused variables as possible
erasure :: [Fun] -> Compile TCM [Fun]
erasure fs = do
    orgRel <- gets (relevantArgs . importedModules)
    (rels, erasureState) <- flip runStateT (ErasureState orgRel M.empty) $ do
        mapM_ initiate fs
        fu <- gets funs
        M.mapKeys (fromMaybe __IMPOSSIBLE__ . flip M.lookup fu) <$> step 1
    modifyEI $ \s -> s { relevantArgs = M.mapKeys funName rels }
    concat <$> mapM (\f -> map (rem (relevancies erasureState)) <$> check f (M.lookup f rels)) fs
  where

    rem rels f@Fun{} = f { funExpr = removeUnused rels (funExpr f) }
    rem _    f       = f
    -- | Perform the worker//wrapper transform
    check :: Fun -> Maybe [Relevance] -> Compile TCM [Fun]
    -- If the function is already marked as to inline we don't need to create a
    -- new function. Also If all arguments are relevant there is nothing to do.
    check f@Fun{} (Just rs) | any isIrr rs && not (funInline f) = do
        f' <- (funName f ++) <$> newName
        let args' = pairwiseFilter (map isRel rs) (funArgs f)
            subs  = pairwiseFilter (map isIrr rs) (funArgs f)
            e'    = foldr (\v e -> subst v "primUnit" e) (funExpr f) subs
        return [ Fun { funInline  = True
                     , funName    = funName f
                     , funQName   = funQName f
                     , funComment = funComment f
                     , funArgs    = funArgs f
                     , funExpr    = App f' $ map Var args'
                     }
               , Fun { funInline  = False
                     , funName    = f'
                     , funQName   = Nothing
                     , funComment = funComment f ++ " [ERASED]"
                     , funArgs    = args'
                     , funExpr    = e'
                     }
               ]
    check f _ = return [f]

removeUnused :: Map Var [Relevance] -> Expr -> Expr
removeUnused rels t = let rem = removeUnused rels
                       in case t of
    Var _         -> t
    Lit _         -> t
    Lam v e       -> Lam v (rem e)
    Con tag qn es -> Con tag qn (map rem es)
    App v es      -> case M.lookup v rels of
       Just re -> App v $ zipWith (\r x -> if isIrr r then UNIT else rem x)
                                  (re ++ repeat Rel) es
       Nothing    -> App v $ map rem es
    Case e brs    -> Case (rem e) (map (\br -> br {brExpr = rem $ brExpr br}) brs)
    If a b c      -> If (rem a) (rem b) (rem c)
    Let v e1 e2   -> lett v (rem e1) (rem e2)
    Lazy e        -> lazy (rem e)
    UNIT          -> t
    IMPOSSIBLE    -> t

-- | Initiate a function's relevancies
initiate :: Fun -> Erasure (Compile TCM) ()
initiate f@(Fun _ name mqname _ args _) = do
    let rels = replicate (length args) Irr
    modify $ \s -> s { relevancies = M.insert name rels (relevancies s)
                     , funs        = M.insert name f (funs s)
                     }
initiate f@(EpicFun {funName = name, funQName = mqname}) = case mqname of
    Just qn -> do
        ty <- lift $ getType qn
        let rels = initialRels ty Rel
        return ()
        modify $ \s -> s { relevancies = M.insert name rels (relevancies s)
                         , funs        = M.insert name f (funs s)
                         }
    Nothing -> return ()

initialRels :: SI.Type -> Relevance -> [Relevance]
initialRels ty rel =
    case SI.unEl ty of
        SI.Pi  a b -> mkRel a : initialRels (SI.unAbs b) rel
        _       -> []
  where
    mkRel :: SI.Dom SI.Type -> Relevance
    mkRel a | ignoreForced (SC.getRelevance a) = Irr
    mkRel a = case SI.unEl (SC.unDom a) of
       SI.Sort _ -> Irr
       _         -> rel

ignoreForced :: SC.Relevance -> Bool
ignoreForced SC.Relevant = False
ignoreForced _           = True

-- | Calculate if a variable is relevant in an expression
relevant :: (Functor m, Monad m) => Var -> Expr -> Erasure m Relevance
relevant var expr = case expr of
    Var v  | v == var  -> return Rel
           | otherwise -> return Irr
    Lit _l      -> return Irr
    Lam _ e     -> relevant var e
    Con _ _ es  -> relevants var es
    App v es | v == var  -> return Rel
             | otherwise -> do
                -- The variable is relevant if it is used in a relevant position
                mvrs <- gets (M.lookup v . relevancies)
                case mvrs of
                  Nothing  -> relevants var es
                  Just vrs ->
                      relevants var
                        $ map snd
                        $ filter ((==) Rel . fst)
                        $ zip (vrs ++ repeat Rel) es
                      -- foldr (||-) Irr <$> zipWith (&&-) (vrs ++ repeat Rel) <$> mapM (relevant var) es
    -- {-
    Case e [br@Branch{}] -> do
        cvars <- foldr (||-) Irr <$> mapM (flip relevant $ brExpr br) (brVars br)
        vare  <- relevant var e
        varbr <- relevant var (brExpr br)
        return ((vare &&- cvars) ||- varbr)
    -- -}
    Case e brs  -> (||-) <$> relevant var e  <*> relevants var (map brExpr brs)
    If a b c    -> relevants var [a,b,c]
    Let x e1 e2 -> (||-) <$> ((&&-) <$> relevant var e1 <*> relevant x e2) <*> relevant var e2
    Lazy e      -> relevant var e
    UNIT        -> return Irr
    IMPOSSIBLE  -> return Irr
  where
    relevants :: (Functor m, Monad m) => Var -> [Expr] -> Erasure m Relevance
    relevants v [] = return Irr
    relevants v (e : es) = do
      r <- relevant v e
      case r of
        Rel -> return r
        _   -> relevants v es
    -- relevants v es = return . foldr (\x y -> x ||- y) Irr =<< mapM (relevant v) es

-- | Try to find a fixpoint for all the functions relevance.
step :: Integer -> Erasure (Compile TCM) (Map Var [Relevance])
step nrOfLoops = do
    s  <- get
    newRels <- (M.fromList <$>) $ forM (M.toList (funs s)) $ \(v, f) -> ((,) v <$>) $ do
               let funRels = fromMaybe __IMPOSSIBLE__ $ M.lookup v (relevancies s)
               case f of
                  EpicFun{} -> return funRels
                  Fun{} -> do
                     forM (zip (funArgs f) (funRels ++ repeat Rel)) $ \ (x, rel) -> case rel of
                        Rel -> return Rel
                        Irr -> do
                          lift $ lift $ reportSDoc "epic.erasure" 10 $ P.text "running erasure:" P.<+> (P.text . show) (funQName f)
                          relevant x (funExpr f)
    let relsm = newRels `M.union` relevancies s
    if relevancies s == relsm
       then return newRels
       else do
         put s {relevancies = relsm}
         step (nrOfLoops + 1)

diff :: (Ord k, Eq a) => Map k a -> Map k a -> [(k,(a,a))]
diff m1 m2 = catMaybes $ zipWith (\(k, x) (_, y) -> if x == y then Nothing else Just (k, (x, y))) (M.toList m1) (M.toList m2)
