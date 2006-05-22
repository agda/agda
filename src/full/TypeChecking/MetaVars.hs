{-# OPTIONS -cpp #-}

module TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Map as Map
import Data.List as List

import Syntax.Common
import qualified Syntax.Info as Info
import Syntax.Internal
import Syntax.Position

import TypeChecking.Monad
import TypeChecking.Monad.Context
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
    store <- getMetaStore
    modify (\st -> st{ stMetaStore = ins x v store })
    wakeupConstraints
  where
    ins x v store = Map.insertWith copy x v store

    copy (Inst _ i) (Open mi o) = Inst mi (copy' i o)
	where
	    copy' (InstV v _) (OpenV t) = InstV v t
	    copy' i _			= i
    copy _ _ = __IMPOSSIBLE__

-- | Generate new meta variable.
--
newMeta :: (MetaId -> a) -> MetaInfo -> OpenMeta -> TCM a
newMeta meta mi initialVal = do
    x <- fresh
    let m = Open mi initialVal
    modify (\st -> st{stMetaStore = Map.insert x m $ stMetaStore st})
    return $ meta x


newSortMeta ::  TCM Sort
newSortMeta = 
    do  i <- createMetaInfo
	newMeta MetaS i OpenS

newTypeMeta :: Sort -> TCM Type
newTypeMeta s =
    do	i <- createMetaInfo
        vs <- allCtxVars
	newMeta (\m -> MetaT m vs) i $ OpenT s

newTypeMeta_ ::  TCM Type
newTypeMeta_  = 
    do  newTypeMeta =<< newSortMeta

newValueMeta ::  Type -> TCM Term
newValueMeta t =
    do	i <- createMetaInfo
        vs <- allCtxVars
	newMeta (\m -> MetaV m vs) i $ OpenV t

newArgsMeta ::  Type -> TCM Args
newArgsMeta (Pi h a b) =
    do	v    <- newValueMeta a
	args <- newArgsMeta (absApp v b)
	return $ Arg h v : args
newArgsMeta _ = return []

newQuestionMark ::  Type -> TCM Term
newQuestionMark t =
    do	m@(MetaV x _) <- newValueMeta t
	ii	      <- fresh
	addInteractionPoint ii x
	return m

newQuestionMarkT ::  Sort -> TCM Type
newQuestionMarkT s =
    do	m@(MetaT x _) <- newTypeMeta s
	ii	      <- fresh
	addInteractionPoint ii x
	return m

newQuestionMarkT_ ::  TCM Type
newQuestionMarkT_ = 
    do  newQuestionMarkT =<< newSortMeta

-- | Used to give an initial value to newMeta.  
--   Get the 'MetaVariable' referred to by a 'MetaId' and make sure that it's
--   'Open'.
getMeta :: MetaId -> Args -> TCM MetaVariable
getMeta x args =
    do	mv <- lookupMeta x
	case mv of
	    Open _ _ -> return mv
	    _	     -> __IMPOSSIBLE__

-- | Generate new metavar of same kind ('Open'X) as that
--     pointed to by @MetaId@ arg.
--
newMetaSame :: MetaId -> Args -> (MetaId -> a) -> TCM a
newMetaSame x args meta =
    do	Open i o <- getMeta x args
	newMeta meta i o

-- | If @restrictParameters ok ps = qs@ then @(\xs -> c qs) ps@ will
--   reduce to @c rs@ where @rs@ is the intersection of @ok@ and @ps@.
restrictParameters :: [Nat] -> [Arg Term] -> Maybe [Arg Term]
restrictParameters ok ps
    | all isVar ps = Just $
	do  (n,p@(Arg _ (Var i []))) <- reverse $ zip [0..] $ reverse ps
	    unless (elem i ok) []
	    return $ Arg NotHidden $ Var n []
    | otherwise	     = Nothing


instV v = Inst __IMPOSSIBLE__ $ InstV v __IMPOSSIBLE__
instT	= Inst __IMPOSSIBLE__ . InstT
instS	= Inst __IMPOSSIBLE__ . InstS

-- | Extended occurs check.
class Occurs a where
    occ :: MetaId -> [Nat] -> a -> TCM a

instance Occurs Term where
    occ m ok v =
	do  v' <- instantiate v
	    case v' of
		Var n vs    ->
		    case findIdx ok n of
			Just n'	-> Var n' <$> occ m ok vs
			Nothing	-> patternViolation [m]
		Lam f vs    -> Lam <$> occ m ok f <*> occ m ok vs
		Lit l	    -> return $ Lit l
		Def c vs    -> Def c <$> occ m ok vs
		Con c vs    -> Con c <$> occ m ok vs
		MetaV m' vs -> occMeta MetaV instV instantiate m ok m' vs
		BlockedV b  -> occ m ok $ blockee b

instance Occurs Type where
    occ m ok t =
	do  t' <- instantiate t
	    case t' of
		El v s	    -> uncurry El <$> occ m ok (v,s)
		Pi h w f    -> uncurry (Pi h) <$> occ m ok (w,f)
		Sort s	    -> Sort <$> occ m ok s
		MetaT m' vs -> occMeta MetaT instT instantiate m ok m' vs
		LamT _	    -> __IMPOSSIBLE__

instance Occurs Sort where
    occ m ok s =
	do  s' <- instantiate s
	    case s' of
		MetaS m' | m == m' -> fail $ "?" ++ show m ++ " occurs in itself"
		Lub s1 s2	   -> uncurry Lub <$> occ m ok (s1,s2)
		_		   -> return s'

occMeta :: (Show a, Data a, Abstract a, Apply a) =>
	   (MetaId -> Args -> a) -> (a -> MetaVariable) -> (a -> TCM a) -> MetaId -> [Nat] -> MetaId -> Args -> TCM a
occMeta meta inst red m ok m' vs
    | m == m'	= fail $ "?" ++ show m ++ " occurs in itself"
    | otherwise	=
	do  vs' <- case restrictParameters ok vs of
		     Nothing  -> patternViolation [m,m']
		     Just vs' -> return vs'
	    when (length vs' /= length vs) $
		do  v1 <-  newMetaSame m' [] (\mi -> meta mi [])
		    let tel = List.map (fmap $ const $ Sort Prop) vs	-- types don't matter here
		    setRef Why m' $ inst $ abstract tel (v1 `apply` vs')
	    let vs0 = List.map rename vs
	    return $ meta m' vs0
    where
	rename (Arg h (Var i [])) =
	    case findIdx ok i of
		Just i'	-> Arg h $ Var i' []
		Nothing	-> Arg h $ Var i []
	rename v = v

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
assign :: (Show a, Data a, Occurs a, Abstract a) => MetaId -> Args -> a -> TCM ()
assign x args = mkQ (fail "assign") (ass instV) `extQ` ass instT `extQ` ass instS where
    ass :: (Show a, Data a, Occurs a, Abstract a) => (a -> MetaVariable) -> a -> TCM ()
    ass inst v = do
	let pshow (Arg NotHidden x) = show x
	    pshow (Arg Hidden x) = "{" ++ show x ++ "}"
        ids <- checkArgs x args
        v' <- occ x ids v
	--debug $ "assign ?" ++ show x ++ " " ++ show args ++ " := " ++ show v'
        --trace ("assign: args="++(show args)++", v'="++(show v')++"\n") $ 
	let tel = List.map (fmap $ const $ Sort Prop) args -- types don't matter here
        setRef Why x $ inst $ abstract tel v'

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


updateMeta :: MetaId -> Term -> TCM ()
updateMeta mI t = 
   do i <- getMetaInfo <$> lookupMeta mI
      withEnv (metaEnv i) (allCtxVars >>= \args -> assign mI args t)
