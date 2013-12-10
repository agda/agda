{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Data where

import Control.Applicative
import Control.Monad

import Data.List (genericTake)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primLevel)
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import qualified Agda.Utils.VarSet as VarSet

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: Info.DefInfo -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i name ps cs =
    traceCall (CheckDataDef (getRange i) (qnameName name) ps cs) $ do -- TODO!! (qnameName)
	let countPars A.DomainFree{} = 1
            countPars (A.DomainFull (A.TypedBindings _ (Arg _ b))) = case b of
              A.TLet{}       -> 0
              A.TBind _ xs _ -> size xs
            npars = sum $ map countPars ps

        -- Add the datatype module
        addSection (qnameToMName name) 0

	-- Look up the type of the datatype.
	t <- instantiateFull =<< typeOfConst name

        -- Make sure the shape of the type is visible
        let unTelV (TelV tel a) = telePi tel a
        t <- unTelV <$> telView t

        -- Top level free vars
        freeVars <- getContextArgs

	-- The parameters are in scope when checking the constructors.
	dataDef <- bindParameters ps t $ \tel t0 -> do

	    -- Parameters are always hidden in constructors
	    let tel' = hideAndRelParams <$> tel
	    -- let tel' = hideTel tel

	    -- The type we get from bindParameters is Θ -> s where Θ is the type of
	    -- the indices. We count the number of indices and return s.
            -- We check that s is a sort.
            (nofIxs, s) <- splitType t0

            when (any (`freeIn` s) [0..nofIxs - 1]) $ do
              err <- fsep [ text "The sort of" <+> prettyTCM name
                          , text "cannot depend on its indices in the type"
                          , prettyTCM t0
                          ]
              typeError $ GenericError $ show err

            s <- return $ raise (-nofIxs) s

            -- the small parameters are taken into consideration for --without-K
            smallPars <- smallParams tel s

            reportSDoc "tc.data.sort" 20 $ vcat
              [ text "checking datatype" <+> prettyTCM name
              , nest 2 $ vcat
                [ text "type (parameters instantiated):   " <+> prettyTCM t0
                , text "type (full):   " <+> prettyTCM t
                , text "sort:   " <+> prettyTCM s
                , text "indices:" <+> text (show nofIxs)
                , text "params:"  <+> text (show ps)
                , text "small params:" <+> text (show smallPars)
                ]
              ]

	    -- Change the datatype from an axiom to a datatype with no constructors.
            let dataDef = Datatype
                  { dataPars       = npars
                  , dataSmallPars  = Perm npars smallPars
                  , dataNonLinPars = Drop 0 $ Perm npars []
                  , dataIxs        = nofIxs
                  , dataInduction  = Inductive
                  , dataClause     = Nothing
                  , dataCons       = []     -- Constructors are added later
                  , dataSort       = s
                  , dataAbstr      = Info.defAbstract i
                  , dataMutual     = []
                  }

	    escapeContext (size tel) $ do
	      addConstant name $
                defaultDefn defaultArgInfo name t dataDef
                -- polarity and argOcc.s determined by the positivity checker

	    -- Check the types of the constructors
            -- collect the non-linear parameters of each constructor
	    nonLins <- mapM (checkConstructor name tel' nofIxs s) cs
            -- compute the ascending list of non-linear parameters of the data type
            let nonLinPars0 = Set.toAscList $ Set.unions $ map Set.fromList nonLins
                -- The constructors are analyzed in the absolute context,
                -- but the data definition happens in the relative module context,
                -- so we apply to the free module variables.
                -- Unfortunately, we lose precision here, since 'abstract', which
                -- is then performed by addConstant, cannot restore the linearity info.
                nonLinPars  = Drop (size freeVars) $ Perm (npars + size freeVars) nonLinPars0

	    -- Return the data definition
	    return dataDef{ dataNonLinPars = nonLinPars }

        let s      = dataSort dataDef
            cons   = map A.axiomName cs  -- get constructor names

	-- If proof irrelevance is enabled we have to check that datatypes in
	-- Prop contain at most one element.
	do  proofIrr <- proofIrrelevance
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> setCurrentRange (getRange cons) $
                                         typeError PropMustBeSingleton
		_		    -> return ()

	-- Add the datatype to the signature with its constructors.
        -- It was previously added without them.
	addConstant name $
          defaultDefn defaultArgInfo name t $
            dataDef{ dataCons = cons }

        -- Andreas 2012-02-13: postpone polarity computation until after positivity check
        -- computePolarity name
    where
      -- Take a type of form @tel -> a@ and return
      -- @size tel@ (number of data type indices) and
      -- @a@ as a sort (either @a@ directly if it is a sort,
      -- or a fresh sort meta set equal to a.
      splitType :: Type -> TCM (Int, Sort)
      splitType t = case ignoreSharing $ unEl t of
        Pi a b -> mapFst (+ 1) <$> do addCtxString (absName b) a $ splitType (absBody b)
        Sort s -> return (0, s)
        _      -> do
          s <- newSortMeta
          equalType t (sort s)
          return (0, s)


-- | A parameter is small if its sort fits into the data sort.
--   @smallParams@ overapproximates the small parameters (in doubt: small).
smallParams :: Telescope -> Sort -> TCM [Int]
smallParams tel s = do
  -- get the types of the parameters
  let as = map (snd . unDom) $ telToList tel
  -- get the big parameters
  concat <$> do
    forM (zip [0..] as) $ \ (i, a) -> do
      -- A type is small if it is not Level or its sort is <= the data sort.
      -- In doubt (unsolvable constraints), a type is small.
      -- So, only if we have a solid error, the type is big.
      localState $ do
        ([] <$ do equalTerm topSort (unEl a) =<< primLevel)  -- NB: if primLevel fails, the next alternative is picked
        <|> ([i] <$ (getSort a `leqSort` s))
        <|> return []
  where
    (<|>) m1 m2 = m1 `catchError_` (const m2)

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
--   Returns the non-linear parameters.
checkConstructor :: QName -> Telescope -> Nat -> Sort
                 -> A.Constructor -> TCM [Int]
checkConstructor d tel nofIxs s (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d tel nofIxs s con
checkConstructor d tel nofIxs s con@(A.Axiom _ i _ c e) =
    traceCall (CheckConstructor d tel s con) $ do
{- WRONG
      -- Andreas, 2011-04-26: the following happens to the right of ':'
      -- we may use irrelevant arguments in a non-strict way in types
      t' <- workOnTypes $ do
-}
        -- check that the type of the constructor is well-formed
        debugEnter c e
	t <- isType_ e
        -- check that the type of the constructor ends in the data type
	n <- getContextSize
	-- OLD: n <- size <$> getContextTelescope
        debugEndsIn t d n
	nonLinPars <- constructs n t d
        debugNonLinPars nonLinPars
        -- check that the sort (universe level) of the constructor type
        -- is contained in the sort of the data type
        -- (to avoid impredicative existential types)
        debugFitsIn s
	t `fitsIn` s
        -- check which constructor arguments are determined by the type ('forcing')
        t' <- addForcingAnnotations t
        debugAdd c t'

        -- add parameters to constructor type and put into signature
        let con = ConHead c [] -- data constructors have no projectable fields
        escapeContext (size tel) $
          addConstant c $
	    defaultDefn defaultArgInfo c (telePi tel t') $
              Constructor (size tel) con d (Info.defAbstract i) Inductive

        return nonLinPars
  where
    debugEnter c e =
      reportSDoc "tc.data.con" 5 $ vcat
        [ text "checking constructor" <+> prettyTCM c <+> text ":" <+> prettyTCM e
        ]
    debugEndsIn t d n =
      reportSDoc "tc.data.con" 15 $ vcat
        [ sep [ text "checking that"
              , nest 2 $ prettyTCM t
              , text "ends in" <+> prettyTCM d
              ]
        , nest 2 $ text "nofPars =" <+> text (show n)
        ]
    debugNonLinPars xs =
      reportSDoc "tc.data.con" 15 $ text $ "these constructor parameters are non-linear: " ++ show xs
    debugFitsIn s =
      reportSDoc "tc.data.con" 15 $ sep
        [ text "checking that the type fits in"
        , nest 2 $ prettyTCM s
        ]
    debugAdd c t =
      reportSDoc "tc.data.con" 5 $ vcat
        [ text "adding constructor" <+> prettyTCM c <+> text ":" <+> prettyTCM t
        ]
checkConstructor _ _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype.
bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameters [] a ret = ret EmptyTel a
bindParameters (A.DomainFull (A.TypedBindings _ (Arg info (A.TBind _ xs _))) : bs) a ret =
  bindParameters ([ A.DomainFree info x | x <- xs ] ++ bs) a ret
bindParameters (A.DomainFull (A.TypedBindings _ (Arg info (A.TLet _ lbs))) : bs) a ret =
  __IMPOSSIBLE__
bindParameters ps0@(A.DomainFree info x : ps) (El _ (Pi arg@(Dom info' a) b)) ret
  -- Andreas, 2011-04-07 ignore relevance information in binding?!
    | argInfoHiding info /= argInfoHiding info' =
	__IMPOSSIBLE__
    | otherwise = addCtx x arg $ bindParameters ps (absBody b) $ \tel s ->
		    ret (ExtendTel arg $ Abs (show x) tel) s
bindParameters bs (El s (Shared p)) ret = bindParameters bs (El s $ derefPtr p) ret
bindParameters (b : bs) t _ = __IMPOSSIBLE__
{- Andreas, 2012-01-17 Concrete.Definitions ensures number and hiding of parameters to be correct
-- Andreas, 2012-01-13 due to separation of data declaration/definition, the user
-- could give more parameters than declared.
bindParameters (b : bs) t _ = typeError $ DataTooManyParameters
-}


-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The first argument is the type of the constructor.
fitsIn :: Type -> Sort -> TCM ()
fitsIn t s = do
  reportSDoc "tc.data.fits" 10 $
    sep [ text "does" <+> prettyTCM t
        , text "of sort" <+> prettyTCM (getSort t)
        , text "fit in" <+> prettyTCM s <+> text "?"
        ]
  -- The code below would be simpler, but doesn't allow datatypes
  -- to be indexed by the universe level.
  -- s' <- instantiateFull (getSort t)
  -- noConstraints $ s' `leqSort` s
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi dom b -> do
      getSort (unDom dom) `leqSort` s
      addCtxString (absName b) dom $ fitsIn (absBody b) (raise 1 s)
    _ -> return () -- getSort t `leqSort` s  -- Andreas, 2013-04-13 not necessary since constructor type ends in data type

-- | Return the parameters that share variables with the indices
-- nonLinearParameters :: Int -> Type -> TCM [Int]
-- nonLinearParameters nPars t =

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype.
--
--   As a side effect, return the parameters that occur free in indices.
--   E.g. in @data Eq (A : Set)(a : A) : A -> Set where refl : Eq A a a@
--   this would include parameter @a@, but not @A@.
--
--   TODO: what if there's a meta here?
constructs :: Int -> Type -> QName -> TCM [Int]
constructs nofPars t q = constrT 0 t
    where
{- OLD
        constrT :: Nat -> Type -> TCM ()
	constrT n (El s v) = constr n s v

        constr :: Nat -> Sort -> Term -> TCM ()
	constr n s v = do
	    v <- reduce v
	    case ignoreSharing v of
		Pi _ (NoAbs _ b) -> constrT n b
		Pi a b	         -> underAbstraction a b $ constrT (n + 1)
		Def d vs
		    | d == q -> checkParams n =<< reduce (take nofPars vs)
						    -- we only check the parameters
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t
-}
        constrT :: Nat -> Type -> TCM [Int]
        constrT n t = do
	    t <- reduce t
	    case ignoreSharing $ unEl t of
		Pi _ (NoAbs _ b)  -> constrT n b
		Pi a b	          -> underAbstraction a b $ constrT (n + 1)
                  -- OR: addCxtString (absName b) a $ constrT (n + 1) (absBody b)
		Def d es | d == q -> do
                  let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                  (pars, ixs) <- normalise $ splitAt nofPars vs
                  -- check that the constructor parameters are the data parameters
                  checkParams n pars
                  -- compute the non-linear parameters
                  m <- getContextSize  -- Note: n /= m if NoAbs encountered
                  let nl = nonLinearParams m pars ixs
                  -- assert that these are correct indices into the parameter vector
                  when (any (< 0) nl) __IMPOSSIBLE__
                  when (any (>= nofPars) nl) __IMPOSSIBLE__
                  return nl
		_ -> typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs = zipWithM_ sameVar vs ps
	    where
                nvs = size vs
		ps = genericTake nvs $ downFrom (n + nvs)

		sameVar arg i
                  -- skip irrelevant parameters
                  | isIrrelevant arg = return ()
		  | otherwise = do
		    t <- typeOfBV i
		    equalTerm t (unArg arg) (var i)

        -- return the parameters (numbered 0,1,...,size pars-1 from left to right)
        -- that occur relevantly in the indices
        nonLinearParams n pars ixs =
          -- compute the free de Bruijn indices in the data indices
          -- ALT: Ignore all sorts?
          let fv = freeVars' FreeConf{ fcIgnoreSorts = IgnoreInAnnotations } ixs
          -- keep relevant ones, convert to de Bruijn levels
          -- note: xs is descending list
              xs = map ((n-1) -) $ VarSet.toList $ relevantVars fv
          -- keep those that correspond to parameters
          -- in ascending list
          in  reverse $ filter (< size pars) xs

{- UNUSED, Andreas 2012-09-13
-- | Force a type to be a specific datatype.
forceData :: QName -> Type -> TCM Type
forceData d (El s0 t) = liftTCM $ do
    t' <- reduce t
    d  <- canonicalName d
    case ignoreSharing t' of
	Def d' _
	    | d == d'   -> return $ El s0 t'
	    | otherwise	-> fail $ "wrong datatype " ++ show d ++ " != " ++ show d'
	MetaV m vs	    -> do
	    Defn {defType = t, theDef = Datatype{dataSort = s}} <- getConstInfo d
	    ps <- newArgsMeta t
	    noConstraints $ leqType (El s0 t') (El s (Def d ps)) -- TODO: need equalType?
	    reduce $ El s0 t'
	_ -> typeError $ ShouldBeApplicationOf (El s0 t) d
-}

-- | Is the type coinductive? Returns 'Nothing' if the answer cannot
-- be determined.

isCoinductive :: Type -> TCM (Maybe Bool)
isCoinductive t = do
  El s t <- normalise t
  case ignoreSharing t of
    Def q _ -> do
      def <- getConstInfo q
      case theDef def of
        Axiom       {} -> return (Just False)
        Function    {} -> return Nothing
        Datatype    { dataInduction = CoInductive } -> return (Just True)
        Datatype    { dataInduction = Inductive   } -> return (Just False)
        Record      {  recInduction = CoInductive } -> return (Just True)
        Record      {  recInduction = Inductive   } -> return (Just False)
        Constructor {} -> __IMPOSSIBLE__
        Primitive   {} -> __IMPOSSIBLE__
    Var   {} -> return Nothing
    Lam   {} -> __IMPOSSIBLE__
    Lit   {} -> __IMPOSSIBLE__
    Level {} -> __IMPOSSIBLE__
    Con   {} -> __IMPOSSIBLE__
    Pi    {} -> return (Just False)
    Sort  {} -> return (Just False)
    MetaV {} -> return Nothing
    Shared{} -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
