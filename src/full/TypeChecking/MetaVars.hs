{-# OPTIONS -cpp #-}

module TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Map as Map
import Data.List as List

import Syntax.Common
import Syntax.Internal

import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Constraints

import Utils.Fresh
import Utils.List
import Utils.Monad

import TypeChecking.Monad.Debug
__debug = debug

#include "../undefined.h"

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over this list @vs@.
--
findIdx :: (Eq a, Monad m) => [a] -> a -> m Int
findIdx vs v = go 0 $ reverse vs where
    go i (v' : vs) | v' == v = return i
    go i (_  : vs)           = go (i + 1) vs
    go _ []                  = fail "findIdx"


-- | Generate [Var n - 1, .., Var 0] for all declarations in the context.
--   Used to make arguments for newly generated metavars.
--
allCtxVars :: TCM Args
allCtxVars = do
    ctx <- asks envContext
    return $ reverse $ List.map (\i -> Arg NotHidden $ Var i []) $ [0 .. length ctx - 1]

setRef :: Data a => a -> MetaId -> MetaVariable -> TCM ()
setRef _ x v = do
    --debug $ "?" ++ show x ++ " := " ++ show v
    store <- gets stMetaStore
    let (cIds, store') = replace x v store
    modify (\st -> st{stMetaStore = store'})
    mapM_ wakeup cIds
  where
    replace x v store =
	case Map.insertLookupWithKey (\_ v _ -> v) x v store of
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

newSortMeta :: TCM Sort
newSortMeta = newMeta MetaS $ UnderScoreS []

newTypeMeta :: Sort -> TCM Type
newTypeMeta s =
    do	vs <- allCtxVars
	newMeta (\m -> MetaT m vs) $ UnderScoreT s []

newTypeMeta_ :: TCM Type
newTypeMeta_ = newTypeMeta =<< newSortMeta

newValueMeta :: Type -> TCM Term
newValueMeta t =
    do	vs <- allCtxVars
	newMeta (\m -> MetaV m vs) $ UnderScoreV t []

newQuestionMark :: Type -> TCM Term
newQuestionMark t =
    do	vs <- allCtxVars
	newMeta (\m -> MetaV m vs) $ HoleV t []

newQuestionMarkT :: Sort -> TCM Type
newQuestionMarkT s =
    do	vs <- allCtxVars
	newMeta (\m -> MetaT m vs) $ HoleT s []

newQuestionMarkT_ :: TCM Type
newQuestionMarkT_ = newQuestionMarkT =<< newSortMeta

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
	mv   -> error $ "getMeta: ?" ++ show x ++ " = " ++ show mv

-- | Generate new metavar of same kind (@Hole@X or @UnderScore@X) as that
--     pointed to by @MetaId@ arg.
--
newMetaSame :: MetaId -> Args -> (MetaId -> a) -> TCM a
newMetaSame x args meta = do
    v <- getMeta x args
    newMeta meta v

-- | If @restrictParameters ok ps = qs@ then @(\xs -> c qs) ps@ will
--   reduce to @c rs@ where @rs@ is the intersection of @ok@ and @ps@.
restrictParameters :: [Nat] -> [Arg Term] -> Maybe [Arg Term]
restrictParameters ok ps
    | all isVar ps = Just $
	do  (n,p@(Arg _ (Var i []))) <- reverse $ zip [0..] $ reverse ps
	    unless (elem i ok) []
	    return $ Arg NotHidden $ Var n []
    | otherwise	     = Nothing


-- | Extended occurs check
--

class Occurs a where
    occ :: MetaId -> [Nat] -> a -> TCM a

instance Occurs Term where
    occ m ok v =
	do  v' <- reduceM v
	    case v' of
		Var n vs    ->
		    case findIdx ok n of
			Just n'	-> Var n' <$> occ m ok vs
			Nothing	-> patternViolation [m]
		Lam f []    -> flip Lam [] <$> occ m ok f
		Lit l	    -> return $ Lit l
		Def c vs    -> Def c <$> occ m ok vs
		Con c vs    -> Con c <$> occ m ok vs
		MetaV m' vs -> occMeta MetaV InstV m ok m' vs
		Lam f _	    -> __IMPOSSIBLE__

instance Occurs Type where
    occ m ok t =
	do  t' <- instType t
	    case t' of
		El v s	    -> uncurry El <$> occ m ok (v,s)
		Pi h w f    -> uncurry (Pi h) <$> occ m ok (w,f)
		Sort s	    -> Sort <$> occ m ok s
		MetaT m' vs -> occMeta MetaT InstT m ok m' vs
		LamT _	    -> __IMPOSSIBLE__	-- ?

instance Occurs Sort where
    occ m ok s =
	do  s' <- instSort s
	    case s' of
		MetaS m' | m == m' -> fail $ "?" ++ show m ++ " occurs in itself"
		Lub s1 s2	   -> uncurry Lub <$> occ m ok (s1,s2)
		_		   -> return s'

occMeta :: (Show a, Data a) => (MetaId -> Args -> a) -> (a -> MetaVariable) -> MetaId -> [Nat] -> MetaId -> Args -> TCM a
occMeta meta inst m ok m' vs
    | m == m'	= fail $ "?" ++ show m ++ " occurs in itself"
    | otherwise	=
	do  vs' <- case restrictParameters ok vs of
		     Nothing  -> patternViolation [m,m']
		     Just vs' -> return vs'
	    when (length vs' /= length vs) $
		do  v1 <-  newMetaSame m' [] (\mi -> meta mi [])
		    setRef Why m' $ inst $ abstract vs (v1 `apply` vs')
	    return $ meta m' vs

instance Occurs a => Occurs (Abs a) where
    occ m ok (Abs s x) = Abs s <$> occ m (List.map (+1) ok ++ [0]) x

instance Occurs a => Occurs (Arg a) where
    occ m ok (Arg h x) = Arg h <$> occ m ok x

instance (Occurs a, Occurs b) => Occurs (a,b) where
    occ m ok (x,y) = (,) <$> occ m ok x <*> occ m ok y

instance Occurs a => Occurs [a] where
    occ m ok xs = mapM (occ m ok) xs


-- | Assign to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assign :: (Show a, Data a, Occurs a) => MetaId -> Args -> a -> TCM ()
assign x args = mkQ (fail "assign") (ass InstV) `extQ` (ass InstT) where
    ass :: (Show a, Data a, Occurs a) => (a -> MetaVariable) -> a -> TCM ()
    ass inst v = do
	let pshow (Arg NotHidden x) = show x
	    pshow (Arg Hidden x) = "{" ++ show x ++ "}"
	store <- gets stMetaStore
        ids <- checkArgs x args
        v' <- occ x ids v
	--debug $ "assign ?" ++ show x ++ " " ++ show args ++ " := " ++ show v'
        --trace ("assign: args="++(show args)++", v'="++(show v')++"\n") $ 
        setRef Why x $ inst $ abstract args v'

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg-- done
--     to not define equality on @Term@.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
--
checkArgs :: MetaId -> Args -> TCM [Nat]
checkArgs x args =
    case validParameters args of
	Just ids    -> return $ reverse ids
	Nothing	    -> patternViolation [x]

-- 	= return = go [] args where
--     go ids  []           = return $ reverse ids
--     go done (Arg _ arg : args) = case arg of 
--         Var i [] | not $ elem i done -> go (i:done) args
--         _                         -> patternViolation x 

-- | Check that the parameters to a meta variable are distinct variables.
validParameters :: Monad m => Args -> m [Nat]
validParameters args
    | all isVar args && distinct vars	= return $ reverse vars
    | otherwise				= fail "invalid parameters"
    where
	vars = [ i | Arg _ (Var i []) <- args ]

isVar :: Arg Term -> Bool
isVar (Arg _ (Var _ [])) = True
isVar _			 = False

