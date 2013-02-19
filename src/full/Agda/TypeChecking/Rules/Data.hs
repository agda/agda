{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Data where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans

import Data.List (genericTake)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Free
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Interaction.Options

import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple

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
              A.TNoBind{}   -> 1
              A.TBind _ xs _ -> size xs
            npars = sum $ map countPars ps

        -- Add the datatype module
        addSection (qnameToMName name) 0

	-- Look up the type of the datatype.
	t <- instantiateFull =<< typeOfConst name

        -- Make sure the shape of the type is visible
        let unTelV (TelV tel a) = telePi tel a
        t <- unTelV <$> telView t

	-- The parameters are in scope when checking the constructors.
	dataDef <- bindParameters ps t $ \tel t0 -> do

	    -- Parameters are always hidden in constructors
	    let tel' = hideTel tel

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

            reportSDoc "tc.data.sort" 20 $ vcat
              [ text "checking datatype" <+> prettyTCM name
              , nest 2 $ vcat
                [ text "type (parameters instantiated):   " <+> prettyTCM t0
                , text "type (full):   " <+> prettyTCM t
                , text "sort:   " <+> prettyTCM s
                , text "indices:" <+> text (show nofIxs)
                , text "params:"  <+> text (show ps)
                ]
              ]

	    -- Change the datatype from an axiom to a datatype with no constructors.
            let dataDef = Datatype { dataPars           = npars
                                   , dataIxs            = nofIxs
                                   , dataInduction      = Inductive
                                   , dataClause         = Nothing
                                   , dataCons           = []     -- Constructors are added later
				   , dataSort           = s
                                   , dataAbstr          = Info.defAbstract i
{-
                                   -- determined by the positivity checker:
                                   , dataPolarity       = []
                                   , dataArgOccurrences = []
-}
                                   , dataMutual         = []
                                   }

	    escapeContext (size tel) $ do
	      addConstant name ( Defn defaultArgInfo name t [] [] (defaultDisplayForm name) 0 noCompiledRep dataDef )

	    -- Check the types of the constructors
	    mapM_ (checkConstructor name tel' nofIxs s) cs

	    -- Return the data definition
	    return dataDef

        let nofIxs = dataIxs dataDef
            s      = dataSort dataDef

	-- If proof irrelevance is enabled we have to check that datatypes in
	-- Prop contain at most one element.
	do  proofIrr <- proofIrrelevance
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> setCurrentRange (getRange $ map conName cs) $
                                        typeError PropMustBeSingleton
                  where conName (A.Axiom _ _ c _) = c
                        conName (A.ScopedDecl _ (d:_)) = conName d
                        conName _ = __IMPOSSIBLE__
		_		    -> return ()

	-- Add the datatype to the signature with its constructors. It was previously
	-- added without them.
	addConstant name (Defn defaultArgInfo name t [] [] (defaultDisplayForm name) 0 noCompiledRep $
                            dataDef { dataCons = map cname cs }
			 )
        -- Andreas 2012-02-13: postpone polarity computation until after positivity check
        -- computePolarity name
    where
	cname (A.ScopedDecl _ [d]) = cname d
	cname (A.Axiom _ _ x _)	   = x
	cname _			   = __IMPOSSIBLE__ -- constructors are axioms

	hideTel  EmptyTel		  = EmptyTel
	hideTel (ExtendTel a tel) = ExtendTel (hideAndRelParams a) $ hideTel <$> tel

        splitType :: Type -> TCM (Int, Sort)
        splitType t = case ignoreSharing $ unEl t of
          Pi a b -> ((+ 1) -*- id) <$> do addCtxString (absName b) a $ splitType (absBody b)
          Sort s -> return (0, s)
	  _      -> do
            s <- newSortMeta
            equalType t (sort s)
            return (0, s)

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Telescope -> Nat -> Sort
                 -> A.Constructor -> TCM ()
checkConstructor d tel nofIxs s (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d tel nofIxs s con
checkConstructor d tel nofIxs s con@(A.Axiom i _ c e) =
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
	n <- size <$> getContextTelescope
        debugEndsIn t d n
	constructs n t d
        -- check that the sort (universe level) of the constructor type
        -- is contained in the sort of the data type
        -- (to avoid impredicative existential types)
        debugFitsIn s
	t `fitsIn` s
        -- check which constructor arguments are determined by the type ('forcing')
        t' <- addForcingAnnotations t
        debugAdd c t'
{-
        return t'
-}
        -- add parameters to constructor type and put into signature
        escapeContext (size tel)
	    $ addConstant c
	    $ Defn defaultArgInfo c (telePi tel t') [] [] (defaultDisplayForm c) 0 noCompiledRep
	    $ Constructor (size tel) c d (Info.defAbstract i) Inductive
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
bindParameters (A.DomainFull (A.TypedBindings _ (Arg info (A.TNoBind _))) : bs) a ret = do
  x <- freshNoName_
  bindParameters (A.DomainFree info x : bs) a ret
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
  t <- instantiateFull t
  s' <- instantiateFull (getSort t)
  reportSDoc "tc.data.fits" 10 $
    sep [ text "does" <+> prettyTCM t
        , text "of sort" <+> prettyTCM s'
        , text "fit in" <+> prettyTCM s <+> text "?"
        ]
  -- The line below would be simpler, but doesn't allow datatypes
  -- to be indexed by the universe level.
--   noConstraints $ s' `leqSort` s
  case ignoreSharing $ unEl t of
    Pi arg@(Dom info a) _ -> do
      let s' = getSort a
      s' `leqSort` s
      x <- freshName_ (argName t)
      let v  = Arg info $ var 0
          t' = piApply (raise 1 t) [v]
      addCtx x arg $ fitsIn t' (raise 1 s)
    _		     -> return ()

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype.
--   TODO: what if there's a meta here?
constructs :: Int -> Type -> QName -> TCM ()
constructs nofPars t q = constrT 0 t
    where
        constrT :: Nat -> Type -> TCM ()
	constrT n (El s v) = constr n s v

        constr :: Nat -> Sort -> Term -> TCM ()
	constr n s v = do
	    v <- reduce v
	    case ignoreSharing v of
		Pi _ (NoAbs _ b) -> constrT n b
		Pi a b	-> underAbstraction a b $ \t ->
			   constrT (n + 1) t
		Def d vs
		    | d == q -> checkParams n =<< reduce (take nofPars vs)
						    -- we only check the parameters
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs = zipWithM_ sameVar vs ps
	    where
--		ps = reverse [ i | (i,_) <- zip [n..] vs ]
                nvs = size vs
		ps = genericTake nvs $ downFrom (n + nvs)

		sameVar arg i
                  -- skip irrelevant parameters
                  | isArgInfoIrrelevant (argInfo arg) = return ()
		  | otherwise = do
		    t <- typeOfBV i
		    equalTerm t (unArg arg) (var i)

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
        Record      {} -> return (Just False)
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
