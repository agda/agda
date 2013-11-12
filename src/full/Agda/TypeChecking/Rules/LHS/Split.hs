{-# LANGUAGE CPP, PatternGuards, ScopedTypeVariables #-}

module Agda.TypeChecking.Rules.LHS.Split where

import Control.Applicative
import Control.Monad.Error

import Data.Maybe (fromMaybe)
import Data.Monoid (mempty, mappend)
import Data.List
import Data.Traversable hiding (mapM, sequence)

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info as A

import Agda.TypeChecking.Monad hiding (SplitError)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.MetaVars

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Tuple
import qualified Agda.Utils.Pretty as P

#include "../../../undefined.h"
import Agda.Utils.Impossible

-- | TODO: move to Agda.Syntax.Abstract.View
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = (x :) -*- id $ asView p
asView p	     = ([], p)

-- | TODO: move somewhere else
expandLitPattern :: A.NamedArg A.Pattern -> TCM (A.NamedArg A.Pattern)
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
          let zero  = A.ConP cinfo (A.AmbQ [setRange r $ conName z]) []
              suc p = A.ConP cinfo (A.AmbQ [setRange r $ conName s]) [defaultNamedArg p]
              info  = A.PatRange r
              cinfo = A.ConPatInfo False info
              p'    = foldr ($) zero $ genericReplicate n suc
          return $ foldr (A.AsP info) p' xs
      _ -> return p

-- | Split a problem at the first constructor pattern which is
--   actually of datatype type.
--
--   Or, if there is no constructor pattern left and the rest type
--   is a record type and the first rest pattern is a projection
--   pattern, split the rest type.
--
--   Implicit patterns should have been inserted.

splitProblem ::
  Maybe QName -- ^ The definition we are checking at the moment.
  -> Problem  -- ^ The current state of the lhs patterns.
  -> TCM (Either SplitError SplitProblem)
splitProblem mf (Problem ps (perm, qs) tel pr) = do
    reportSLn "tc.lhs.split" 20 $ "initiating splitting"
      ++ maybe "" ((" for definition " ++) . show) mf
    reportSDoc "tc.lhs.split" 30 $ sep
      [ nest 2 $ text "ps   =" <+> sep (map (P.parens <.> prettyA) ps)
      , nest 2 $ text "qs   =" <+> sep (map (P.parens <.> prettyTCM . namedArg) qs)
      , nest 2 $ text "perm =" <+> prettyTCM perm
      , nest 2 $ text "tel  =" <+> prettyTCM tel
      ]
    runErrorT $
      splitP ps (permute perm $ zip [0..] $ allHoles qs) tel
  where
    -- Result splitting
    splitRest :: ProblemRest -> ErrorT SplitError TCM SplitProblem
    splitRest (ProblemRest (p : ps) b) | Just f <- mf = do
      let failure   = lift $ typeError $ CannotEliminateWithPattern p $ unArg b
          notProjP  = lift $ typeError $ NotAProjectionPattern p
          notRecord = failure -- lift $ typeError $ ShouldBeRecordType $ unArg b
      lift $ reportSDoc "tc.lhs.split" 20 $ sep
        [ text "splitting problem rest"
        , nest 2 $ text "pattern         p =" <+> prettyA p
        , nest 2 $ text "eliminates type b =" <+> prettyTCM b
        ]
      -- If the pattern is not a projection pattern, that's an error.
      -- Probably then there were too many arguments.
      caseMaybe (isProjP p) failure $ \ d -> do
        -- So it is a projection pattern (d = projection name), is it?
        caseMaybeM (lift $ isProjection d) notProjP $
          \ Projection{projProper = Just d, projFromType = _, projIndex = n} -> do
            -- If projIndex==0, then the projection is already applied
            -- to the record value (like in @open R r@), and then it
            -- is no longer a projection but a record field.
            unless (n > 0) notProjP
            lift $ reportSLn "tc.lhs.split" 90 "we are a projection pattern"
            -- If the target is not a record type, that's an error.
            -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
            caseMaybeM (lift $ isRecordType $ unArg b) notRecord $
              \ (r, vs, Record{ recFields = fs }) -> do
                {- NO LONGER NEEDED, BUT KEEP
                -- normalize projection name (could be from a module app)
                d <- lift $ do
                  v <- stripLambdas =<< normalise (Def d [])
                  case v of
                    Def d _ -> return d
                    _       -> do
                      reportSDoc "impossible" 10 $ sep
                        [ text   "unexpected result " <+> prettyTCM v
                        , text $ "when normalizing projection " ++ show d
                        ]
                      reportSDoc "impossible" 50 $ sep
                        [ text $ "raw: " ++ show v
                        ]
                      __IMPOSSIBLE__
                -}
                lift $ reportSDoc "tc.lhs.split" 20 $ sep
                  [ text $ "we are of record type r  = " ++ show r
                  , text   "applied to parameters vs = " <+> prettyTCM vs
                  , text $ "and have fields       fs = " ++ show fs
                  , text $ "original proj         d  = " ++ show d
                  ]
                -- Get the field decoration.
                -- If the projection pattern @d@ is not a field name, that's an error.
                argd <- maybe failure return $ find ((d ==) . unArg) fs
                let es = patternsToElims perm qs
                -- the record "self" is the definition f applied to the patterns
                fvs <- lift $ freeVarsToApply f
                let self = defaultArg $ Def f (map Apply fvs) `applyE` es
                -- get the type of projection d applied to "self"
                dType <- lift $ defType <$> getConstInfo d  -- full type!
                -- dType <- lift $ typeOfConst d  -- WRONG: we apply to parameters ourselves!!
                lift $ reportSDoc "tc.lhs.split" 20 $ sep
                  [ text "we are              self = " <+> prettyTCM (unArg self)
                  , text "being projected by dType = " <+> prettyTCM dType
                  ]
                return $ SplitRest argd $ dType `apply` (vs ++ [self])
    -- if there are no more patterns left in the problem rest, there is nothing to split:
    splitRest _ = throwError $ NothingToSplit

    -- Stripping initial lambdas from a normalized term
    stripLambdas :: Term -> TCM Term
    stripLambdas v = case ignoreSharing v of
        Lam _ b -> addCtxString_ (absName b) $ stripLambdas (absBody b)
        v       -> return v

    -- | In @splitP aps iqs tel@,
    --   @aps@ are the user patterns on which we are splitting (inPats),
    --   @ips@ are the one-hole patterns of the current split state (outPats)
    --   in one-to-one correspondence with the pattern variables
    --   recorded in @tel@.
    splitP :: [A.NamedArg A.Pattern] -> [(Int, OneHolePatterns)] -> Telescope -> ErrorT SplitError TCM SplitProblem
    -- the next two cases violate the one-to-one correspondence of qs and tel
    splitP _	    []		 (ExtendTel _ _)	 = __IMPOSSIBLE__
    splitP _	    (_:_)	  EmptyTel		 = __IMPOSSIBLE__
    -- no more patterns?  pull them from the rest
    splitP []	     _		  _			 = splitRest pr
    -- patterns but no types for them?  Impossible.
    splitP ps	    []		  EmptyTel		 = __IMPOSSIBLE__
    -- pattern with type?  Let's get to work:
    splitP (p : ps) ((i, q) : qs) tel0@(ExtendTel a tel) = do
      liftTCM $ reportSDoc "tc.lhs.split" 30 $ sep
        [ text "splitP looking at pattern"
        , nest 2 $ text "p =" <+> prettyA p
        , nest 2 $ text "a =" <+> prettyTCM a
        ]
      let tryAgain = splitP (p : ps) ((i, q) : qs) tel0
      p <- lift $ expandLitPattern p
      case asView $ namedArg p of

        -- Case: projection pattern.  That's an error.
        (_, p') | Just{} <- isProjP p' -> do
           typeError $ CannotEliminateWithPattern p (telePi tel0 $ unArg $ restType pr)

        -- Case: literal pattern
	(xs, p@(A.LitP lit))  -> do
          -- Note that, in the presence of --without-K, this branch is
          -- based on the assumption that the types of literals are
          -- not indexed.

          -- Andreas, 2010-09-07 cannot split on irrelevant args
          when (unusableRelevance $ getRelevance a) $
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
	(xs, p@(A.ConP ci (A.AmbQ cs) args)) -> do
          let tryInstantiate a'
                | [c] <- cs = do
                    -- Type is blocked by a meta and constructor is unambiguous,
                    -- in this case try to instantiate the meta.
                  ok <- lift $ do
                    Constructor{ conData = d } <- theDef <$> getConstInfo c
                    dt     <- defType <$> getConstInfo d
                    vs     <- newArgsMeta dt
                    Sort s <- ignoreSharing . unEl <$> reduce (apply dt vs)
                    (True <$ noConstraints (equalType a' (El s $ Def d $ map Apply vs)))
                      `catchError` \_ -> return False
                  if ok then tryAgain else keepGoing
                | otherwise = keepGoing
          -- ifBlockedType reduces the type
          ifBlockedType (unDom a) (const tryInstantiate) $ \ a' -> do
	  case ignoreSharing $ unEl a' of

            -- Subcase: split type is a Def
	    Def d es	-> do
	      def <- liftTCM $ theDef <$> getConstInfo d
              unless (defIsRecord def) $
                -- cannot split on irrelevant or non-strict things
                when (unusableRelevance $ getRelevance a) $ do
                  -- Andreas, 2011-10-04 unless allowed by option
                  allowed <- liftTCM $ optExperimentalIrrelevance <$> pragmaOptions
                  unless allowed $ typeError $ SplitOnIrrelevant p a

              let mp = case def of
                        Datatype{dataPars = np} -> Just np
                        Record{recPars = np}    -> Just np
                        _                       -> Nothing
              case mp of
                Nothing -> keepGoing
                Just np -> do
                  let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
		  liftTCM $ traceCall (CheckPattern p EmptyTel (unDom a)) $ do  -- TODO: wrong telescope
                  -- Check that we construct something in the right datatype
                  c <- do
                      cs' <- mapM canonicalName cs
                      d'  <- canonicalName d
                      let cons def = case theDef def of
                            Datatype{dataCons = cs} -> cs
                            Record{recConHead = c}      -> [conName c]
                            _                       -> __IMPOSSIBLE__
                      cs0 <- cons <$> getConstInfo d'
                      case [ c | (c, c') <- zip cs cs', elem c' cs0 ] of
                        [c]   -> return c
                        []    -> typeError $ ConstructorPatternInWrongDatatype (head cs) d
                        cs    -> -- if there are more than one we give up (they might have different types)
                          typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d cs
{-
                          typeError $ GenericError $
                            "Can't resolve overloaded constructors targeting the same datatype (" ++ show d ++ "):" ++
                            unwords (map show cs)
-}
		  let (pars, ixs) = genericSplitAt np vs
		  reportSDoc "tc.lhs.split" 10 $
		    vcat [ sep [ text "splitting on"
			       , nest 2 $ fsep [ prettyA p, text ":", prettyTCM a ]
			       ]
			 , nest 2 $ text "pars =" <+> fsep (punctuate comma $ map prettyTCM pars)
			 , nest 2 $ text "ixs  =" <+> fsep (punctuate comma $ map prettyTCM ixs)
			 ]

                  -- Andreas, 2013-03-22 fixing issue 279
                  -- To resolve ambiguous constructors, Agda always looks up
                  -- their original definition and reconstructs the parameters
                  -- from the type @Def d vs@ we check against.
                  -- However, the constructor could come from a module instantiation
                  -- with some of the parameters already fixed.
                  -- Agda did not make sure the two parameter lists coincide,
                  -- so we add a check here.
                  -- I guess this issue could be solved more systematically,
                  -- but the extra check here is non-invasive to the existing code.
                  checkParsIfUnambiguous cs d pars

                  whenM (optWithoutK <$> pragmaOptions) $
                    wellFormedIndices a'

		  return $ Split mempty
				 xs
				 (argFromDom $ fmap (Focus c (A.patImplicit ci) args (getRange p) q i d pars ixs) a)
				 (fmap (\ tel -> Problem ps () tel __IMPOSSIBLE__) tel)
            -- Subcase: split type is not a Def
	    _	-> keepGoing
        -- Case: neither literal nor constructor pattern
	p -> keepGoing
      where
	keepGoing = do
          r <- underAbstraction a tel $ \tel -> splitP ps qs tel
          case r of
            SplitRest{} -> return r
	    Split p1 xs foc p2 -> do
  	      let p0 = Problem [p] () (ExtendTel a (EmptyTel <$ tel)) mempty
	      return $ Split (mappend p0 p1) xs foc p2
{- OLD
	keepGoing = do
	  let p0 = Problem [p] () (ExtendTel a (EmptyTel <$ tel)) mempty
	  Split p1 xs foc p2 <- underAbstraction a tel $ \tel -> splitP ps qs tel
	  return $ Split (mappend p0 p1) xs foc p2
-}

-- | @checkParsIfUnambiguous [c] d pars@ checks that the data/record type
--   behind @c@ is has initial parameters (coming e.g. from a module instantiation)
--   that coincide with an prefix of @pars@.
checkParsIfUnambiguous :: [QName] -> QName -> Args -> TCM ()
checkParsIfUnambiguous [c] d pars = do
  dc <- getConstructorData c
  a  <- reduce (Def dc [])
  case ignoreSharing a of
    Def d0 es -> do -- compare parameters
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reportSDoc "tc.lhs.split" 40 $
        vcat [ nest 2 $ text "d                   =" <+> prettyTCM d
             , nest 2 $ text "d0 (should be == d) =" <+> prettyTCM d0
             , nest 2 $ text "dc                  =" <+> prettyTCM dc
             ]
      -- when (d0 /= d) __IMPOSSIBLE__ -- d could have extra qualification
      t <- typeOfConst d
      compareArgs [] t (Def d []) vs (take (length vs) pars)
    _ -> __IMPOSSIBLE__
checkParsIfUnambiguous _ _ _ = return ()

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
    Def d es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
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
  constructorApplication (Con c conArgs) (El _ (Def d es)) = do
    conDef  <- getConInfo c
    dataDef <- getConstInfo d

    let noPars = case theDef dataDef of
          Datatype { dataPars = n } -> n
          Record   { recPars  = n } -> n
          _                         -> __IMPOSSIBLE__
        dataArgs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
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

  constructorApplications :: [(I.Arg Term, I.Dom Type)] -> TCM (Maybe [Nat])
  constructorApplications args = do
    xs <- mapM (\(e, t) -> do
                   t <- reduce (unDom t)
                   constructorApplication (unArg e) (ignoreSharingType t))
               args
    return (concat <$> sequence xs)

-- | @args \`withTypesFrom\` t@ returns the arguments @args@ paired up
-- with their types, taken from @t@, which is assumed to be a @length
-- args@-ary pi.
--
-- Precondition: @t@ has to start with @length args@ pis.

withTypesFrom :: Args -> Type -> TCM [(I.Arg Term, I.Dom Type)]
[]           `withTypesFrom` _ = return []
(arg : args) `withTypesFrom` t = do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi a b -> ((arg, a) :) <$>
              args `withTypesFrom` absApp b (unArg arg)
    _      -> __IMPOSSIBLE__
