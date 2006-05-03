{-# OPTIONS -cpp #-}

module TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Map as Map
import Data.List as List

import Syntax.Internal
import Syntax.Internal.Walk
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Constraints
import Utils.Fresh

#include "../undefined.h"

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over this list @vs@.
--
findIdx :: (Eq a, Monad m) => [a] -> a -> m Int
findIdx vs v = go 0 (reverse vs) where
    go i (v' : vs) | v' == v = return i
    go i (_  : vs)           = go (i + 1) vs
    go _ []                  = fail "findIdx"


-- | Generate [Var 0 Duh, Var 1 Duh, ...] for all declarations in context.
--   Used to make arguments for newly generated @Type@ metavars.
--
allCtxVars :: TCM Args
allCtxVars = do
    ctx <- ask
    return $ List.map (\i -> Var i []) $ [0 .. length ctx - 1]

setRef :: Data a => a -> MetaId -> MetaVariable -> TCM ()
setRef _ x v = do
    store <- gets stMetaStore
    let (cIds, store') = replace x v store
    modify (\st -> st{stMetaStore = store'})
    mapM_ wakeup cIds
  where
    replace x v store =
	case Map.updateLookupWithKey (\_ _ -> Just v) x store of
	    (Just var, store')	-> (getCIds var, store')
	    _			-> __IMPOSSIBLE__

-- | Generate new meta variable.
--   The @MetaVariable@ arg (2nd arg) is meant to be either @UnderScore@X or @Hole@X.
--
newMeta :: (MetaId -> a) -> MetaVariable -> TCM a
newMeta meta initialVal = do
    x <- fresh
    modify (\st -> st{stMetaStore = Map.insert x initialVal $ stMetaStore st})
    return $ meta x

-- | Used to give an initial value to newMeta.  
--   The constraint list will be filled-in as needed during assignment.
--
getMeta :: MetaId -> Args -> TCM MetaVariable
getMeta x args = do
    store <- gets stMetaStore
    case Map.lookup x store of
        Just (UnderScoreV _ _) -> do
            s <- newMeta MetaS $ UnderScoreS []
            a <- newMeta (\x -> MetaT x args) $ UnderScoreT s [] 
            return $ (UnderScoreV a [])
        Just (UnderScoreT s _) -> return $ (UnderScoreT s [])
        Just (UnderScoreS _) -> return $ (UnderScoreS [])
        Just (HoleV a _) -> do
            s <- newMeta MetaS $ UnderScoreS []
            a <- newMeta (\x -> MetaT x args) $ UnderScoreT s [] 
            return $ (HoleV a [])
        Just (HoleT s _) -> return $ (HoleT s [])
	_   -> __IMPOSSIBLE__

-- | Generate new metavar of same kind (@Hole@X or @UnderScore@X) as that
--     pointed to by @MetaId@ arg.
--
newMetaSame :: MetaId -> Args -> (MetaId -> a) -> TCM a
newMetaSame x args meta = do
    (v) <- getMeta x args
    newMeta meta v

-- | Extended occurs check
--
occ :: MetaId -> [Int] -> GenericM TCM
occ y okVars v = go v where
    go v = walk (mkM occVal) v --`extM` occTyp
    occMVar inst meta x args =
        if x == y then fail "occ"
        else do
            (args', newArgs) <- occMVarArgs x args
            --trace ("occMVar: okVars="++(show okVars)++", args="++(show args)++", args'="++(show args')++", newArgs="++(show newArgs)++"\n") $ 
            if length args' == length newArgs
                then return ()
                else lift $ lift $ do
                    v1 <-  newMetaSame x args meta -- !!! is args right here?
                    --trace ("occMVar prune: v1="++(show v1)++"\n") $ 
                    setRef Why x $ inst $ abstract args (addArgs newArgs v1)
            endWalk $ addArgs args' (meta x)
    occMVarArgs x args = ocA ([],[]) [] (length args - 1) args where
        ocA res _ _ [] = return res
        ocA (old, new) ids idx (arg:args) = do
            v <- lift $ lift $ reduceM arg
            case v of
                Var i [] | not $ elem i ids -> 
                    --trace ("occMVarArgs: findIdx "++(show okVars)++" "++(show i)++" = "++(show $ (findIdx okVars i:: Maybe Int))++"\n") $ 
                    case findIdx okVars i of
                        Just j -> ocA (old++[Var j []], new++[Var idx []]) (i:ids) (idx-1) args
                        Nothing -> ocA (old++[arg], new) ids (idx-1) args
                _ -> patternViolation x
    occVal v = do
        v' <- lift $ lift $ reduceM v 
        case v' of 
            Var i args -> do
                j <- findIdx okVars i
                return $ addArgs args (Var j []) -- continues walking along args
            MetaV x args -> occMVar InstV (\x -> MetaV x []) x args -- !!! MetaV should have no args?
            _ -> return v'
    occTyp v = do
        v' <- lift $ lift $ instType v
        case v' of
           MetaT x args -> occMVar (InstT) (\x -> MetaT x []) x args -- !!! MetaT should have no args?
           _ -> return v'
           
        
-- | Assign to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assign :: MetaId -> [Value] -> GenericQ (TCM ())
assign x args = mkQ (fail "assign") (ass InstV) `extQ` (ass InstT) where
    ass :: (Show a, Data a) => (a -> MetaVariable) -> a -> TCM ()
    ass inst v = do
        ids <- checkArgs x args
        v' <- occ x ids v    
        --trace ("assign: args="++(show args)++", v'="++(show v')++"\n") $ 
        setRef Why x $ inst $ abstract args v'

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg-- done
--     to not define equality on @Value@.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
--
checkArgs :: MetaId -> [Value] -> TCM [Int]
checkArgs x args = go [] args where
    go ids  []           = return $ reverse ids
    go done (arg : args) = case arg of 
        Var i [] | not $ elem i done -> go (i:done) args
        _                         -> patternViolation x 



