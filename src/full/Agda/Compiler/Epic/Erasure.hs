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

import Agda.TypeChecking.Monad.Base (MonadTCM)

data Relevancy
  = Irr
  | Rel
  | DontKnow
  deriving (Eq, Ord, Show)

isIrr :: Relevancy -> Bool
isIrr Irr      = True
isIrr Rel      = False
isIrr DontKnow = True

isRel :: Relevancy -> Bool
isRel = not . isIrr

-- | Irrelevancy "and"
(&&-) :: Relevancy -> Relevancy -> Relevancy
Rel      &&- _        = Rel
_        &&- Rel      = Rel
DontKnow &&- a        = a
a        &&- DontKnow = a
Irr      &&- Irr      = Irr -- If both arguments are irrelevant, then surely we
                            -- have something irrelevant.

data ErasureState = ErasureState
  { relevancies :: Map Var [Relevancy]
  , funs        :: Map Var Fun
  }

type Erasure = StateT ErasureState

-- | Try to find as many unused variables as possible
erasure :: MonadTCM m => [Fun] -> Compile m [Fun]
erasure fs = do
    rels <- flip evalStateT (ErasureState M.empty M.empty) $ do
        mapM_ initiate fs
        fu <- gets funs
        M.mapKeys (fromJust . flip M.lookup fu) <$> step
    fmap concat $ mapM (\f -> check f (M.lookup f rels)) fs
  where
    -- | Perform the worker//wrapper transform
    check :: MonadTCM m => Fun -> Maybe [Relevancy] -> Compile m [Fun]
    -- If the function is already marked as to inline we don't need to create a
    -- new function. Also If all arguments are relevant there is nothing to do.
    check f (Just rs) | any isIrr rs && not (funInline f) = do
        f' <- newName
        let args' = pairwiseFilter (map isRel rs) (funArgs f)
            subs  = pairwiseFilter (map isIrr rs) (funArgs f)
            e'    = foldr (\v e -> subst v "primUnit" e) (funExpr f) subs
        return [ Fun { funInline  = True
                     , funName    = funName f
                     , funComment = funComment f
                     , funArgs    = funArgs f
                     , funExpr    = App f' $ map Var args'
                     }
               , Fun { funInline  = False
                     , funName    = f'
                     , funComment = funComment f ++ " [ERASED]"
                     , funArgs    = args'
                     , funExpr    = e'
                     }
               ]
    check f _ = return [f]

-- | Initiate a function's relevancies (all DontKnow)
initiate :: Monad m => Fun -> Erasure m ()
initiate f@(Fun _ name _ args _) =
    modify $ \s -> s { relevancies = M.insert name (replicate (length args) DontKnow) (relevancies s)
                     , funs        = M.insert name f (funs s)
                     }
initiate (EpicFun {})            = return ()

-- | Calculate if a variable is relevant in an expression
relevant :: (Functor m, Monad m) => Var -> Expr -> Erasure m Relevancy
relevant var expr = case expr of
    Var v  | v == var  -> return Rel
           | otherwise -> return Irr
    Lit _l       -> return Irr
    Lam _ e     -> relevant var e
    Con _ _ es  -> relevants var es
    App v es | v == var  -> return Rel
             | otherwise -> do
                -- The variable is relevant if it is used in a relevant position
                mvrs <- gets (M.lookup v . relevancies)
                case mvrs of
                  Nothing  -> relevants var es
                  Just vrs -> relevants var
                            $ pairwiseFilter (map isRel vrs ++ repeat True {- Needs ETA expansion -}) es
    Case e brs  -> (&&-) <$> relevant var e  <*> relevants var (map brExpr brs)
    If a b c    -> relevants var [a,b,c]
    Let _ e1 e2 -> (&&-) <$> relevant var e1 <*> relevant var e2
    Lazy e      -> relevant var e
    UNIT        -> return Irr
    IMPOSSIBLE  -> return Irr
  where
    relevants :: (Functor m, Monad m) => Var -> [Expr] -> Erasure m Relevancy
    relevants v es = foldM (\x y -> return $ x &&- y) Irr =<< mapM (relevant v) es

-- | Try to find a fixpoint for all the functions relevancy.
step :: (Monad m, Functor m) => Erasure m (Map Var [Relevancy])
step = do
    s  <- get
    rels <- forM (M.toList (relevancies s)) $ \(v, _) -> do
               let f = fromJust $ M.lookup v (funs s)
               (,) v <$> mapM (flip relevant (funExpr f)) (funArgs f)
    let relsm = M.fromList rels
    if relevancies s == relsm
       then return relsm
       else do
           put s {relevancies = relsm}
           step
