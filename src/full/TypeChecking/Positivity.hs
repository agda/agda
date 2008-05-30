{-# OPTIONS_GHC -cpp -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}

-- | Check that a datatype is strictly positive.
module TypeChecking.Positivity (checkStrictlyPositive) where

import Prelude hiding (foldr, mapM_, mapM, elem, concat)

import Control.Applicative
import Control.Monad hiding (mapM_, mapM)
import Control.Monad.Trans (liftIO)
import Control.Monad.State hiding (mapM_, mapM)
import Control.Monad.Error hiding (mapM_, mapM)
import Data.Foldable
import Data.Traversable
import Data.Set (Set)
import Data.Monoid
import qualified Data.Set as Set
import qualified Data.Map as Map

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Errors
import TypeChecking.Reduce
import TypeChecking.Pretty

import Utils.Monad

#include "../undefined.h"
import Utils.Impossible

-- | Check that a set of mutually recursive datatypes are strictly positive.
checkStrictlyPositive :: [QName] -> TCM ()
checkStrictlyPositive ds = flip evalStateT noAssumptions $ do
    cs <- concat <$> mapM constructors ds
    mapM_ check cs
    where
	check (d, c) = do
	  a <- lift $ defAbstract <$> getConstInfo d
	  inMode a $ do
	    t <- lift (normalise =<< typeOfConst c)
	    checkPos ds (OccCon d c) t

	inMode :: IsAbstract -> PosM a -> PosM a
	inMode a m = do
	  s	 <- get
	  (x, s) <- lift $ mode a $ runStateT m s
	  put s
	  return x
	  where
	    mode AbstractDef = inAbstractMode
	    mode ConcreteDef = inConcreteMode

	constructors :: QName -> StateT Assumptions TCM [(QName, QName)]
	constructors d = do
	    def <- lift $ theDef <$> getConstInfo d
	    case def of
		Datatype{dataCons = cs} -> return $ zip (repeat d) cs
		_                       -> __IMPOSSIBLE__

-- | Assumptions about arguments to datatypes
type Assumptions = Set (QName, Nat)

noAssumptions :: Assumptions
noAssumptions = Set.empty

type PosM = StateT Assumptions TCM

isAssumption :: QName -> Nat -> PosM Bool
isAssumption q i = do
    a <- get
    return $ Set.member (q,i) a

assume :: QName -> Nat -> PosM ()
assume q i = modify $ Set.insert (q,i)

-- | @checkPos ds d c t@: Check that @ds@ only occurs stricly positively in the
--   type @t@ of the constructor @c@ of datatype @d@.
checkPos :: [QName] -> (OccPos -> Occ) -> Type -> PosM ()
checkPos ds mkReason t = mapM_ check ds
    where
	check d = case Map.lookup d defs of
	    Nothing  -> return ()    -- non-recursive
	    Just ocs
		| NonPositive `elem` ocs -> lift $ typeError $
		    NotStrictlyPositive d [mkReason NonPositively]
		| otherwise		 -> mapM_ (uncurry checkPosArg') args
		where
		    args = [ (q, i) | Argument q i <- Set.toList ocs ]
	    where
		checkPosArg' q i = checkPosArg q i
		    `catchError` \e -> case e of
			TypeError _ Closure{clValue = NotStrictlyPositive _ reason} ->
			    lift $ typeError
				 $ NotStrictlyPositive d
				 $ mkReason (ArgumentTo (fromIntegral i) q) : reason
			_   -> throwError e

	defs = unMap $ getDefs $ arguments t
	arguments t = case unEl t of
	    Pi a b  -> a : arguments (absBody b)
	    Fun a b -> a : arguments b
	    _	    -> []

-- | Check that a particular argument occurs strictly positively in the
--   definition of a datatype.
checkPosArg :: QName -> Nat -> PosM ()
checkPosArg d i = unlessM (isAssumption d i) $ do
    assume d i
    lift $ reportSLn "tc.pos.arg" 20 $ "checkPosArg " ++ show d ++ " " ++ show i
    def <- lift $ theDef <$> getConstInfo d
    case def of
	Datatype{dataCons = cs} -> do
	    xs <- lift $ map (qnameFromList . (:[])) <$>
		  replicateM (fromIntegral $ i + 1) (freshName_ "dummy")
	    let x = xs !! fromIntegral i
		args = map (Arg NotHidden . flip Def []) xs
	    let check c = do
		    t <- lift $ normalise =<< (defType <$> getConstInfo c)
		    checkPos [x] (OccCon d c) (t `piApply` args)

	    mapM_ check cs
        Function{funClauses = cs} -> zipWithM_ (checkPosClause d i) [0..] cs
	_   -> lift $ typeError $ NotStrictlyPositive d []

checkPosClause :: QName -> Nat -> Nat -> Clause -> PosM ()
checkPosClause f i n (Clause _ _ ps body) = do
  x    <- lift $ freshName_ "checkMe"
  args <- concat <$> zipWithM (mkArg $ def x) [0..] ps
  lift $ reportSLn "tc.pos.clause" 20 $ "checkPosClause\n" ++ unlines (map ("  " ++) [ show body, show args, show ps ])
  case body `apply` args of
    Body b -> do
      let t = -- b -> Prop
              El Prop $ Fun (Arg NotHidden $ El Prop b) (El Prop $ Sort Prop)
      checkPos [qnameFromList [x]] (OccClause f $ fromIntegral n) t
    NoBody -> return ()
    _     -> __IMPOSSIBLE__
  where
    mkArgs :: Term -> Nat -> [Arg Pattern] -> PosM Args
    mkArgs me j ps = concat <$> mapM (mkArg me j) ps

    mkArg :: Term -> Nat -> Arg Pattern -> PosM Args
    mkArg me j (Arg _ p) = map (Arg NotHidden) <$> mkPat me j p

    mkPat me j (VarP _)
                | i == j = return [me]
    mkPat _ j _ | i == j = lift $ typeError $ NotStrictlyPositive f []
    mkPat me j (ConP c ps) = map unArg <$> mkArgs me j ps
    mkPat me j (DotP _) = return []
    mkPat me j (VarP _) = (:[]) <$> dummy
    mkPat me j (LitP l) = return []

    def = flip Def [] . qnameFromList . (:[])
    dummy = lift $ def <$> freshName_ "dummy"

data Occurence = Positive | NonPositive | Argument QName Nat
    deriving (Show, Eq, Ord)

newtype Map k v = Map { unMap :: Map.Map k v }
type Defs = Map QName (Set Occurence)

instance (Ord k, Monoid v) => Monoid (Map k v) where
    mempty = Map Map.empty
    mappend (Map ds1) (Map ds2) = Map (Map.unionWith mappend ds1 ds2)

instance Ord k => Functor (Map k) where
    fmap f (Map m) = Map $ fmap f m

makeNegative :: Defs -> Defs
makeNegative = fmap (const $ Set.singleton NonPositive)

makeArgument :: QName -> Nat -> Defs -> Defs
makeArgument q i = fmap (Set.insert (Argument q i) . Set.delete Positive)

singlePositive :: QName -> Defs
singlePositive q = Map $ Map.singleton q (Set.singleton Positive)

class HasDefinitions a where
    getDefs :: a -> Defs

instance HasDefinitions Term where
    getDefs t = case ignoreBlocking t of
	Var _ args   -> makeNegative $ getDefs args
	Lam _ t	     -> getDefs t
	Lit _	     -> mempty
	Def q args   -> mappend (getDefs q)
				(mconcat $ zipWith (makeArgument q) [0..] $ map getDefs args)
	Con q args   -> getDefs (q, args)
	Pi a b	     -> mappend (makeNegative $ getDefs a) (getDefs b)
	Fun a b	     -> mappend (makeNegative $ getDefs a) (getDefs b)
	Sort _	     -> mempty
	MetaV _ args -> getDefs args
	BlockedV _   -> __IMPOSSIBLE__

instance HasDefinitions Type where
    getDefs = getDefs . unEl

instance HasDefinitions QName where
    getDefs = singlePositive

instance (HasDefinitions a, HasDefinitions b) => HasDefinitions (a,b) where
    getDefs (x,y) = mappend (getDefs x) (getDefs y)

instance (Functor f, Foldable f, HasDefinitions a) =>
	 HasDefinitions (f a) where
    getDefs = foldr mappend mempty . fmap getDefs

