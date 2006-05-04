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
import TypeChecking.Monad.Debug
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Constraints

import Utils.Fresh
import Utils.List

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
    ctx <- asks envContext
    return $ List.map (\i -> Arg NotHidden $ Var i []) $ [0 .. length ctx - 1]

setRef :: Data a => a -> MetaId -> MetaVariable -> TCM ()
setRef _ x v = do
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

newTypeMeta :: TCM Type
newTypeMeta =
    do	s  <- newSortMeta
	vs <- allCtxVars
	newMeta (\m -> MetaT m vs) $ UnderScoreT s []

newValueMeta :: Type -> TCM Term
newValueMeta t =
    do	vs <- allCtxVars
	newMeta (\m -> MetaV m vs) $ UnderScoreV t []

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
data MetaThing a =
	MetaThing (MetaId -> Args -> a)
		  (a -> MetaVariable)
		  MetaId Args

class Occurs a where
    occ :: MetaId -> [Nat] -> a -> TCM ()

instance Occurs Term where
    occ m ok v =
	do  v' <- reduceM v
	    case v of
		Var n vs    -> occ m ok vs
		Lam f []    -> occ m ok f
		Lit l	    -> return ()
		Def c vs    -> occ m ok vs
		Con c vs    -> occ m ok vs
		MetaV m' vs -> occ m ok $ MetaThing MetaV InstV m' vs
		Lam f _	    -> __IMPOSSIBLE__

instance Occurs Type where
    occ m ok t =
	do  t' <- instType t
	    case t' of
		El v s	    -> occ m ok (v,s)
		Pi _ w f    -> occ m ok (w,f)
		Sort s	    -> occ m ok s
		MetaT m' vs -> occ m ok $ MetaThing MetaT InstT m' vs
		LamT _	    -> __IMPOSSIBLE__	-- ?

instance Occurs Sort where
    occ m ok s =
	do  s' <- instSort s
	    case s' of
		MetaS m' | m == m' -> fail $ "?" ++ show m ++ " occurs in itself"
		Lub s1 s2	   -> occ m ok (s1,s2)
		_		   -> return ()

instance Data a => Occurs (MetaThing a) where
    occ m ok (MetaThing meta inst m' vs)
	| m == m'	= fail $ "?" ++ show m ++ " occurs in itself"
	| otherwise	=
	    do  vs' <- case restrictParameters ok vs of
			 Nothing  -> patternViolation [m,m']
			 Just vs' -> return vs'
		v1 <-  newMetaSame m' [] (\mi -> meta mi [])
		setRef Why m' $ inst $ abstract vs (v1 `apply` vs')

instance Occurs a => Occurs (Abs a) where
    occ m ok (Abs _ x) = occ m (0 : List.map (+1) ok) x

instance Occurs a => Occurs (Arg a) where
    occ m ok (Arg _ x) = occ m ok x

instance (Occurs a, Occurs b) => Occurs (a,b) where
    occ m ok (x,y) = occ m ok x >> occ m ok y

instance Occurs a => Occurs [a] where
    occ m ok xs = mapM_ (occ m ok) xs


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
	debug $ "assign " ++ unwords (show x : List.map pshow args) ++ " := " ++ show v
	store <- gets stMetaStore
	debug $ "  " ++ show x ++ " = " ++ show (Map.lookup x store :: Maybe MetaVariable)
        ids <- checkArgs x args
        occ x ids v    
        --trace ("assign: args="++(show args)++", v'="++(show v')++"\n") $ 
        setRef Why x $ inst $ abstract args v

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
	Just ids    -> return ids
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

