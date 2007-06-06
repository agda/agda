{-# OPTIONS -fglasgow-exts -cpp #-}

module TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Data.Generics
import Data.Map (Map)
import Data.Set (Set)
import Data.List as List hiding (sort)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Syntax.Common
import qualified Syntax.Info as Info
import Syntax.Internal
import Syntax.Position

import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Constraints
import TypeChecking.Errors
import TypeChecking.Free
import TypeChecking.Records

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Conversion
#endif

import Utils.Fresh
import Utils.List
import Utils.Monad
import Utils.Size

import TypeChecking.Monad.Debug

#include "../undefined.h"

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over the list.
--
findIdx :: Eq a => [a] -> a -> Maybe Int
findIdx vs v = findIndex (==v) (reverse vs)

-- | Check whether a meta variable is a place holder for a blocked term.
isBlockedTerm :: MonadTCM tcm => MetaId -> tcm Bool
isBlockedTerm x = do
    report 12 $ "is " ++ show x ++ " a blocked term? "
    i <- mvInstantiation <$> lookupMeta x
    let r = case i of
	    BlockedConst _ -> True
	    InstV _	   -> False
	    InstS _	   -> False
	    Open	   -> False
    reportLn 12 $ if r then "yes" else "no"
    return r

class HasMeta t where
    metaInstance :: MonadTCM tcm => t -> tcm MetaInstantiation
    metaVariable :: MetaId -> Args -> t

instance HasMeta Term where
    metaInstance = return . InstV
    metaVariable = MetaV

instance HasMeta Sort where
    metaInstance     = return . InstS
    metaVariable x _ = MetaS x

-- | The instantiation should not be an 'InstV' or 'InstS' and the 'MetaId'
--   should point to something 'Open' or a 'BlockedConst'.
(=:) :: (MonadTCM tcm, HasMeta t) => MetaId -> t -> tcm ()
x =: t = do
    i <- metaInstance t
    store <- getMetaStore
    modify $ \st -> st { stMetaStore = ins x i store }
    etaExpandListeners x
    wakeupConstraints
  where
    ins x i store = Map.adjust (inst i) x store
    inst i mv = mv { mvInstantiation = i }

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()
assignTerm = (=:)

newSortMeta :: MonadTCM tcm => tcm Sort
newSortMeta = 
    do  i <- createMetaInfo
	MetaS <$> newMeta i normalMetaPriority (IsSort ())

newTypeMeta :: MonadTCM tcm => Sort -> tcm Type
newTypeMeta s = El s <$> newValueMeta (sort s)

newTypeMeta_ ::  MonadTCM tcm => tcm Type
newTypeMeta_  = newTypeMeta =<< newSortMeta

-- | Create a new metavariable, possibly η-expanding in the process.
newValueMeta ::  MonadTCM tcm => Type -> tcm Term
newValueMeta t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx (telePi_ tel t) vs

newValueMetaCtx :: MonadTCM tcm => Type -> Args -> tcm Term
newValueMetaCtx t ctx = do
  m@(MetaV i _) <- newValueMetaCtx' t ctx
  etaExpandMeta i
  instantiateFull m

-- | Create a new value meta without η-expanding.
newValueMeta' :: MonadTCM tcm => Type -> tcm Term
newValueMeta' t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx' (telePi_ tel t) vs

-- | Create a new value meta with specific dependencies.
newValueMetaCtx' :: MonadTCM tcm => Type -> Args -> tcm Term
newValueMetaCtx' t vs = do
  i <- createMetaInfo
  x <- newMeta i normalMetaPriority (HasType () $ makeClosed t)
  verbose 50 $ do
    dt <- prettyTCM t
    liftIO $ putStrLn $ "new meta: " ++ show x ++ " : " ++ show dt
  return $ MetaV x vs

newArgsMeta :: MonadTCM tcm => Type -> tcm Args
newArgsMeta t = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newArgsMetaCtx t tel args

newArgsMetaCtx :: MonadTCM tcm => Type -> Telescope -> Args -> tcm Args
newArgsMetaCtx (El s tm) tel ctx = do
  tm <- reduce tm
  case funView tm of
      FunV (Arg h a) _  -> do
	  v    <- newValueMetaCtx (telePi_ tel a) ctx
	  args <- newArgsMetaCtx (El s tm `piApply` [Arg h v]) tel ctx
	  return $ Arg h v : args
      NoFunV _    -> return []

-- | Create a metavariable of record type. This is actually one metavariable
--   for each field.
newRecordMeta :: MonadTCM tcm => QName -> Args -> tcm Term
newRecordMeta r pars = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newRecordMetaCtx r pars tel args

newRecordMetaCtx :: MonadTCM tcm => QName -> Args -> Telescope -> Args -> tcm Term
newRecordMetaCtx r pars tel ctx = do
  ftel	 <- flip apply pars <$> getRecordFieldTypes r
  fields <- newArgsMetaCtx (telePi_ ftel $ sort Prop) tel ctx
  return $ Con r fields

newQuestionMark :: MonadTCM tcm => Type -> tcm Term
newQuestionMark t = do
  m@(MetaV x _) <- newValueMeta' t
  ii		<- fresh
  addInteractionPoint ii x
  return m

-- | Construct a blocked constant if there are constraints.
blockTerm :: MonadTCM tcm => Type -> Term -> tcm Constraints -> tcm Term
blockTerm t v m = do
    cs <- solveConstraints =<< m
    if List.null cs
	then return v
	else do
	    i	  <- createMetaInfo
	    vs	  <- getContextArgs
	    tel   <- getContextTelescope
	    x	  <- newMeta i lowMetaPriority (HasType () $ makeClosed $ telePi_ tel t)
			    -- ^^ we don't instantiate blocked terms
	    store <- getMetaStore
	    modify $ \st -> st { stMetaStore = ins x (BlockedConst $ abstract tel v) store }
	    c <- escapeContext (size tel) $ guardConstraint (return cs) (UnBlock x)
            verbose 20 $ do
                dx  <- prettyTCM (MetaV x [])
                dv  <- escapeContext (size tel) $ prettyTCM $ abstract tel v
                dcs <- mapM prettyTCM cs
                liftIO $ putStrLn $ "blocked " ++ show dx ++ " := " ++ show dv
                liftIO $ putStrLn $ "     by " ++ show dcs
	    addConstraints c
	    return $ MetaV x vs
  where
    ins x i store = Map.adjust (inst i) x store
    inst i mv = mv { mvInstantiation = i }

-- | Eta expand metavariables listening on the current meta.
etaExpandListeners :: MonadTCM tcm => MetaId -> tcm ()
etaExpandListeners m = do
  ms <- getMetaListeners m
  clearMetaListeners m	-- we don't really have to do this
  mapM_ etaExpandMeta ms

-- | Eta expand a metavariable.
etaExpandMeta :: MonadTCM tcm => MetaId -> tcm ()
etaExpandMeta m = do
  HasType _ o <- mvJudgement <$> lookupMeta m
  a <- getOpen o
  TelV tel b <- telViewM a
  let args	 = [ Arg h $ Var i []
		   | (i, Arg h _) <- reverse $ zip [0..] $ reverse $ telToList tel
		   ]
  case unEl b of
    BlockedV b	-> listenToMeta m (blockingMeta b)
    MetaV i _	-> listenToMeta m i
    Def r ps	->
      ifM (isRecord r) (do
	u <- newRecordMetaCtx r ps tel args
	inContext [] $ addCtxTel tel $ do
	  verbose 20 $ do
	    du <- prettyTCM u
	    liftIO $ putStrLn $ "eta expanding: " ++ show m ++ " --> " ++ show du
	  noConstraints $ assignV b m args u  -- should never produce any constraints
      ) $ return ()
    _		-> return ()

  return ()

-- | Generate new metavar of same kind ('Open'X) as that
--     pointed to by @MetaId@ arg.
--
newMetaSame :: MonadTCM tcm => MetaId -> (MetaId -> a) -> tcm a
newMetaSame x meta =
    do	mv <- lookupMeta x
	meta <$> newMeta (getMetaInfo mv) (mvPriority mv) (mvJudgement mv)

-- | Extended occurs check.
class Occurs t where
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Term -> TCM Term #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Type -> TCM Type #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Sort -> TCM Sort #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Arg Term -> TCM (Arg Term) #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Arg Type -> TCM (Arg Type) #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Abs Term -> TCM (Abs Term) #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> Abs Type -> TCM (Abs Type) #-}
    {-# SPECIALIZE occurs :: (Occurs a, Occurs b) => TCM () -> MetaId -> (a, b) -> TCM (a, b) #-}
    {-# SPECIALIZE occurs :: TCM () -> MetaId -> [Arg Term] -> TCM [Arg Term] #-}
    occurs :: TCM () -> MetaId -> t -> TCM t

{-# SPECIALIZE occursCheck :: MetaId -> Term -> TCM Term #-}
occursCheck :: (MonadTCM tcm, Occurs a) => MetaId -> a -> tcm a
occursCheck m = liftTCM . occurs (typeError $ MetaOccursInItself m) m

instance Occurs Term where
    occurs abort m v = do
	v <- reduce v
	case v of
	    -- Don't fail on blocked terms
	    BlockedV b	-> occurs' patternViolation v
	    _		-> occurs' abort v
	where
	    occurs' abort v = case ignoreBlocking v of
		Var i vs    -> Var i <$> occ vs
		Lam h f	    -> Lam h <$> occ f
		Lit l	    -> return v
		Def c vs    -> Def c <$> occ vs
		Con c vs    -> Con c <$> occ vs
		Pi a b	    -> uncurry Pi <$> occ (a,b)
		Fun a b	    -> uncurry Fun <$> occ (a,b)
		Sort s	    -> Sort <$> occ s
		MetaV m' vs -> do
		    when (m == m') abort
		    -- Don't fail on flexible occurrence
		    MetaV m' <$> occurs patternViolation m vs
		BlockedV _  -> __IMPOSSIBLE__
		where
		    occ x = occurs abort m x

instance Occurs Type where
    occurs abort m (El s v) = uncurry El <$> occurs abort m (s,v)

instance Occurs Sort where
    occurs abort m s =
	do  s' <- reduce s
	    case s' of
		MetaS m'  -> when (m == m') abort >> return s'
		Lub s1 s2 -> uncurry Lub <$> occurs abort m (s1,s2)
		Suc s	  -> Suc <$> occurs abort m s
		Type _	  -> return s'
		Prop	  -> return s'

instance Occurs a => Occurs (Abs a) where
    occurs abort m (Abs s x) = Abs s <$> occurs abort m x

instance Occurs a => Occurs (Arg a) where
    occurs abort m (Arg h x) = Arg h <$> occurs abort m x

instance (Occurs a, Occurs b) => Occurs (a,b) where
    occurs abort m (x,y) = (,) <$> occurs abort m x <*> occurs abort m y

instance Occurs a => Occurs [a] where
    occurs abort m xs = mapM (occurs abort m) xs

abortAssign :: MonadTCM tcm => tcm a
abortAssign =
    do	s <- get
	liftTCM $ throwError $ AbortAssign s

handleAbort :: MonadTCM tcm => TCM a -> TCM a -> tcm a
handleAbort h m = liftTCM $
    m `catchError` \e ->
	case e of
	    AbortAssign s -> do put s; h
	    _		  -> throwError e

-- | Assign to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assignV :: MonadTCM tcm => Type -> MetaId -> Args -> Term -> tcm Constraints
assignV t x args v =
    handleAbort handler $ do
	verbose 10 $ do
	    d1 <- prettyTCM (MetaV x args)
	    d2 <- prettyTCM v
	    debug $ show d1 ++ " := " ++ show d2

	-- We don't instantiate blocked terms
	whenM (isBlockedTerm x) patternViolation	-- TODO: not so nice

	-- Check that the arguments are distinct variables
        verbose 20 $ do
            let pr (Var n []) = show n
                pr (Def c []) = show c
                pr _          = ".."
            liftIO $ putStrLn $ "args: " ++ unwords (map (pr . unArg) args)
            
	ids <- checkArgs x args

	verbose 15 $ do
	    d <- prettyTCM v
	    debug $ "preparing to instantiate: " ++ show d

	-- Check that the x doesn't occur in the right hand side
	v <- liftTCM $ occursCheck x v

	reportLn 15 "passed occursCheck"

	-- Check that all free variables of v are arguments to x
	let fv	  = freeVars v
	    idset = Set.fromList ids
	    badrv = Set.toList $ Set.difference (rigidVars fv) idset
	    badfv = Set.toList $ Set.difference (flexibleVars fv) idset
	-- If a rigid variable is not in ids there is no hope
	unless (null badrv) $ typeError $ MetaCannotDependOn x ids (head badrv)
	-- If a flexible variable is not in ids we can wait and hope that it goes away
	unless (null badfv) $ do
	  verbose 15 $ do
	    bad <- mapM (prettyTCM . flip Var []) badfv
	    liftIO $ putStrLn $ "bad flexible variables: " ++ show bad
	  patternViolation

	reportLn 15 "passed free variable check"

	-- Rename the variables in v to make it suitable for abstraction over ids.
	v' <- do
	    -- Basically, if
	    --   Γ	 = a b c d e
	    --   ids = d b e
	    -- then
	    --   v' = (λ a b c d e. v) _ 1 _ 2 0
	    tel  <- getContextTelescope
	    args <- map (Arg NotHidden) <$> getContextTerms
	    let iargs = reverse $ zipWith (rename $ reverse ids) [0..] $ reverse args
		v'    = raise (size ids) (abstract tel v) `apply` iargs
	    return v'

	let extTel i m = do
	      tel <- m
	      t	  <- typeOfBV i
	      x	  <- nameOfBV i
	      return $ ExtendTel (Arg NotHidden t) (Abs (show x) tel)
	tel' <- foldr extTel (return EmptyTel) ids

	verbose 15 $ do
	    d <- prettyTCM (abstract tel' v')
	    debug $ "final instantiation: " ++ show d

	-- Perform the assignment (and wake constraints). Metas
	-- are top-level so we do the assignment at top-level.
	n <- size <$> getContextTelescope
	escapeContext n $ x =: abstract tel' v'
	return []
    where
	rename ids i arg = case findIndex (==i) ids of
	    Just j  -> fmap (const $ Var j []) arg
	    Nothing -> fmap (const __IMPOSSIBLE__) arg	-- we will end up here, but never look at the result

	handler :: MonadTCM tcm => tcm Constraints
	handler = do
	    reportLn 10 $ "Oops. Undo " ++ show x ++ " := ..."
	    equalTerm t (MetaV x args) v

assignS :: MonadTCM tcm => MetaId -> Sort -> tcm Constraints
assignS x s =
    handleAbort (equalSort (MetaS x) s) $ do
	occursCheck x s
	x =: s
	return []

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg-- done
--     to not define equality on @Term@.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
--
checkArgs :: MonadTCM tcm => MetaId -> Args -> tcm [Nat]
checkArgs x args =
    case validParameters args of
	Just ids    -> return $ reverse ids
	Nothing	    -> patternViolation

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


updateMeta :: (MonadTCM tcm, Data a, Occurs a, Abstract a) => MetaId -> a -> tcm ()
updateMeta mI t = 
    do	mv <- lookupMeta mI
	withMetaInfo (getMetaInfo mv) $
	    do	args <- getContextArgs
		cs <- upd mI args (mvJudgement mv) t
		unless (List.null cs) $ fail $ "failed to update meta " ++ show mI
    where
	upd mI args j t = (__IMPOSSIBLE__ `mkQ` updV j `extQ` updS) t
	    where
		updV (HasType _ o) v = do
		  t <- getOpen o
		  assignV (t `piApply` args) mI args v
		updV _ _	     = __IMPOSSIBLE__

		updS s = assignS mI s

