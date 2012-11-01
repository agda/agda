{-# LANGUAGE CPP, PatternGuards #-}

module Agda.TypeChecking.Rules.LHS.Split where

import Control.Applicative
import Control.Monad.Error
import Data.Monoid (mempty, mappend)
import Data.List
import Data.Traversable hiding (mapM, sequence)

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.ProblemRest
-- import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.MetaVars

import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Tuple

#include "../../../undefined.h"
import Agda.Utils.Impossible

-- | TODO: move to Agda.Syntax.Abstract.View
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = (x :) -*- id $ asView p
asView p	     = ([], p)

-- | TODO: move somewhere else
expandLitPattern :: NamedArg A.Pattern -> TCM (NamedArg A.Pattern)
expandLitPattern p = traverse (traverse expand) p
  where
    expand p = case asView p of
      (xs, A.LitP (LitInt r n))
        | n < 0     -> __IMPOSSIBLE__
        | n > 20    -> typeError $ GenericError $
                        "Matching on natural number literals is done by expanding "
                        ++ "the literal to the corresponding constructor pattern, so "
                        ++ "you probably don't want to do it this way."
        | otherwise -> do
          Con z _ <- ignoreSharing <$> primZero
          Con s _ <- ignoreSharing <$> primSuc
          let zero  = A.ConP info (A.AmbQ [setRange r z]) []
              suc p = A.ConP info (A.AmbQ [setRange r s]) [defaultNamedArg p]
              info  = A.PatRange r
              p'    = foldr ($) zero $ genericReplicate n suc
          return $ foldr (A.AsP info) p' xs
      _ -> return p

-- | Split a problem at the first constructor of datatype type. Implicit
--   patterns should have been inserted.
splitProblem :: Problem -> TCM (Either SplitError SplitProblem)
splitProblem (Problem ps (perm, qs) tel pr) = do
    reportS "tc.lhs.split" 20 $ "initiating splitting\n"
    runErrorT $
      splitP ps (permute perm $ zip [0..] $ allHoles qs) tel
  where
    splitP :: [NamedArg A.Pattern] -> [(Int, OneHolePatterns)] -> Telescope -> ErrorT SplitError TCM SplitProblem
    splitP _	    []		 (ExtendTel _ _)	 = __IMPOSSIBLE__
    splitP _	    (_:_)	  EmptyTel		 = __IMPOSSIBLE__
    splitP []	     _		  _			 = throwError $ NothingToSplit
    splitP ps	    []		  EmptyTel		 = __IMPOSSIBLE__
    splitP (p : ps) ((i, q) : qs) tel0@(ExtendTel a tel) = do
      let tryAgain = splitP (p : ps) ((i, q) : qs) tel0
      p <- lift $ expandLitPattern p
      case asView $ namedThing $ unArg p of

        -- Case: literal pattern
	(xs, p@(A.LitP lit))  -> do
          -- Note that, in the presence of --without-K, this branch is
          -- based on the assumption that the types of literals are
          -- not indexed.

          -- Andreas, 2010-09-07 cannot split on irrelevant args
          when (unusableRelevance $ domRelevance a) $
            typeError $ SplitOnIrrelevant p a
	  b <- lift $ litType lit
	  ok <- lift $ do
	      noConstraints (equalType (unDom a) b)
	      return True
	    `catchError` \_ -> return False
	  if ok
	    then return $
	      Split mempty
		    xs
		    (argFromDom $ fmap (LitFocus lit q i) a)
		    (fmap (\ tel -> Problem ps () tel __IMPOSSIBLE__) tel)
	    else keepGoing

        -- Case: constructor pattern
	(xs, p@(A.ConP _ (A.AmbQ cs) args)) -> do
          let tryInstantiate a'
                | [c] <- cs = do
                    -- Type is blocked by a meta and constructor is unambiguous,
                    -- in this case try to instantiate the meta.
                  ok <- lift $ do
                    Constructor{ conData = d } <- theDef <$> getConstInfo c
                    dt     <- defType <$> getConstInfo d
                    vs     <- newArgsMeta dt
                    Sort s <- ignoreSharing . unEl <$> reduce (apply dt vs)
                    (True <$ noConstraints (equalType a' (El s $ Def d vs)))
                      `catchError` \_ -> return False
                  if ok then tryAgain else keepGoing
                | otherwise = keepGoing
          ifBlockedType (unDom a) (const tryInstantiate) $ \ a' -> do
	  case ignoreSharing $ unEl a' of

            -- Subcase: split type is a Def
	    Def d vs	-> do
	      def <- liftTCM $ theDef <$> getConstInfo d
              unless (defIsRecord def) $
                -- cannot split on irrelevant or non-strict things
                when (unusableRelevance $ domRelevance a) $ do
                  -- Andreas, 2011-10-04 unless allowed by option
                  allowed <- liftTCM $ optExperimentalIrrelevance <$> pragmaOptions
                  unless allowed $ typeError $ SplitOnIrrelevant p a

              let mp = case def of
                        Datatype{dataPars = np} -> Just np
                        Record{recPars = np}    -> Just np
                        _                       -> Nothing
              case mp of
                Nothing -> keepGoing
                Just np ->
		  liftTCM $ traceCall (CheckPattern p EmptyTel (unDom a)) $ do  -- TODO: wrong telescope
                  -- Check that we construct something in the right datatype
                  c <- do
                      cs' <- mapM canonicalName cs
                      d'  <- canonicalName d
                      let cons def = case theDef def of
                            Datatype{dataCons = cs} -> cs
                            Record{recCon = c}      -> [c]
                            _                       -> __IMPOSSIBLE__
                      cs0 <- cons <$> getConstInfo d'
                      case [ c | (c, c') <- zip cs cs', elem c' cs0 ] of
                        [c]   -> return c
                        []    -> typeError $ ConstructorPatternInWrongDatatype (head cs) d
                        cs    -> -- if there are more than one we give up (they might have different types)
                          typeError $ GenericError $
                            "Can't resolve overloaded constructors targeting the same datatype (" ++ show d ++ "):" ++
                            unwords (map show cs)

		  let (pars, ixs) = genericSplitAt np vs
		  reportSDoc "tc.lhs.split" 10 $
		    vcat [ sep [ text "splitting on"
			       , nest 2 $ fsep [ prettyA p, text ":", prettyTCM a ]
			       ]
			 , nest 2 $ text "pars =" <+> fsep (punctuate comma $ map prettyTCM pars)
			 , nest 2 $ text "ixs  =" <+> fsep (punctuate comma $ map prettyTCM ixs)
			 ]

                  whenM (optWithoutK <$> pragmaOptions) $
                    wellFormedIndices a'

		  return $ Split mempty
				 xs
				 (argFromDom $ fmap (Focus c args (getRange p) q i d pars ixs) a)
				 (fmap (\ tel -> Problem ps () tel __IMPOSSIBLE__) tel)
            -- Subcase: split type is not a Def
	    _	-> keepGoing
        -- Case: neither literal nor constructor pattern
	p -> keepGoing
      where
	keepGoing = do
	  let p0 = Problem [p] () (ExtendTel a $ fmap (const EmptyTel) tel) mempty
	  Split p1 xs foc p2 <- underAbstraction a tel $ \tel -> splitP ps qs tel
	  return $ Split (mappend p0 p1) xs foc p2

-- | Takes a type, which must be a data or record type application,
-- and checks that the indices are constructors (or literals) applied
-- to distinct variables which do not occur free in the parameters.
-- For the purposes of this check parameters count as constructor
-- arguments; parameters are reconstructed from the given type.
--
-- Precondition: The type must be a data or record type application.

wellFormedIndices :: Type -> TCM ()
wellFormedIndices t = do
  t <- reduce t

  reportSDoc "tc.lhs.split.well-formed" 10 $
    fsep [ text "Checking if indices are well-formed:"
         , nest 2 $ prettyTCM t
         ]

  (pars, ixs) <- normalise =<< case ignoreSharing $ unEl t of
    Def d args -> do
      def       <- getConstInfo d
      typedArgs <- args `withTypesFrom` defType def

      let noPars = case theDef def of
            Datatype { dataPars = n } -> n
            Record   { recPars  = n } -> n
            _                         -> __IMPOSSIBLE__
          (pars, ixs) = genericSplitAt noPars typedArgs
      return (map fst pars, ixs)

    _ -> __IMPOSSIBLE__

  mvs <- constructorApplications ixs
  vs  <- case mvs of
           Nothing -> typeError $
                        IndicesNotConstructorApplications (map fst ixs)
           Just vs -> return vs

  unless (fastDistinct vs) $
    typeError $ IndexVariablesNotDistinct vs (map fst ixs)

  case map fst $ filter snd $ zip vs (map (`freeIn` pars) vs) of
    [] -> return ()
    vs ->
      typeError $ IndicesFreeInParameters vs (map fst ixs) pars

  where
  -- | If the term consists solely of constructors (or literals)
  -- applied to variables (after parameter reconstruction), then the
  -- variables are returned, and otherwise nothing.
  constructorApplication :: Term
                         -> Type  -- ^ The term's type.
                         -> TCM (Maybe [Nat])
  constructorApplication (Var x [])      _ = return (Just [x])
  constructorApplication (Lit {})        _ = return (Just [])
  constructorApplication (Shared p)      t  = constructorApplication (derefPtr p) t
  constructorApplication (Con c conArgs) (El _ (Def d dataArgs)) = do
    conDef  <- getConstInfo c
    dataDef <- getConstInfo d

    let noPars = case theDef dataDef of
          Datatype { dataPars = n } -> n
          Record   { recPars  = n } -> n
          _                         -> __IMPOSSIBLE__
        pars    = genericTake noPars dataArgs
        allArgs = pars ++ conArgs

    reportSDoc "tc.lhs.split.well-formed" 20 $
      fsep [ text "Reconstructed parameters:"
           , nest 2 $
               prettyTCM (Con c []) <+>
               text "(:" <+> prettyTCM (defType conDef) <> text ")" <+>
               text "<<" <+> prettyTCM pars <+> text ">>" <+>
               prettyTCM conArgs
           ]

    constructorApplications =<< allArgs `withTypesFrom` defType conDef

  constructorApplication _ _ = return Nothing

  constructorApplications :: [(Arg Term, Dom Type)] -> TCM (Maybe [Nat])
  constructorApplications args = do
    xs <- mapM (\(e, t) -> constructorApplication (unArg e) (ignoreSharingType $ unDom t))
               args
    return (concat <$> sequence xs)

-- | @args \`withTypesFrom\` t@ returns the arguments @args@ paired up
-- with their types, taken from @t@, which is assumed to be a @length
-- args@-ary pi.
--
-- Precondition: @t@ has to start with @length args@ pis.

withTypesFrom :: Args -> Type -> TCM [(Arg Term, Dom Type)]
[]           `withTypesFrom` _ = return []
(arg : args) `withTypesFrom` t = do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi a b -> ((arg, a) :) <$>
              args `withTypesFrom` absApp b (unArg arg)
    _      -> __IMPOSSIBLE__
