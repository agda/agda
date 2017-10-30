{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Rules.LHS.Split
  ( splitProblem
  ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.Either
import Data.Maybe (fromMaybe)
import qualified Data.List as List
import Data.Traversable hiding (mapM, sequence)
import Data.Foldable (msum)

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate (storeDisambiguatedName)

import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment'(..), nameFieldA)
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (IsProjP(..), MaybePostfixProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views (asView)
import qualified Agda.Syntax.Info as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Errors (dropTopLevelModule)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.LHS.Problem

import Agda.Utils.Either
import Agda.Utils.Except (catchError)
import Agda.Utils.Functor ((<.>))
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.NonemptyList
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | Split a problem at the first constructor pattern which is
--   actually of datatype type.
--
--   Or, if there is no constructor pattern left and the rest type
--   is a record type and the first rest pattern is a projection
--   pattern, split the rest type.
--
--   Implicit patterns should have been inserted.

splitProblem :: forall tcm. (MonadTCM tcm, MonadWriter Blocked_ tcm, MonadDebug tcm)
  => LHSState  -- ^ The current state of the lhs patterns.
  -> ListT tcm SplitProblem
splitProblem (LHSState tel qs (Problem ps pr) b dpi sbe) = do
  do
    reportSLn "tc.lhs.split" 20 $ "initiating splitting"
    reportSDoc "tc.lhs.split" 30 $ sep
      [ nest 2 $ text "ps   =" <+> sep (map (P.parens <.> prettyA) ps)
      , nest 2 $ text "qs   =" <+> sep (map (P.parens <.> prettyTCM . namedArg) qs)
      , nest 2 $ text "tel  =" <+> prettyTCM tel
      ]
    reportSDoc "tc.lhs.split" 60 $ sep
      [ nest 2 $ text "ps  (raw) =" <+> sep (map (P.parens <.> text . show) ps)
      , nest 2 $ text "qs  (raw) =" <+> sep (map (P.parens <.> text . show . namedArg) qs)
      , nest 2 $ text "tel (raw) =" <+> (text . show) tel
      ]
  splitP ps tel
  where
    -- Result splitting
    splitRest :: [NamedArg A.Pattern] -> Arg Type -> ListT tcm SplitProblem
    splitRest (p : ps) b = do
      reportSDoc "tc.lhs.split" 20 $ sep
        [ text "splitting problem rest"
        , nest 2 $ text "pattern         p =" <+> prettyA p
        , nest 2 $ text "eliminates type b =" <+> prettyTCM b
        ]
      reportSDoc "tc.lhs.split" 80 $ sep
        [ nest 2 $ text $ "pattern (raw)   p = " ++ show p
        ]
      -- If the pattern is not a projection pattern, that's an error.
      -- Probably then there were too many arguments.
      caseMaybe (maybePostfixProjP p) failure $ \ (o, ambD@(AmbQ ds)) -> do
        -- So it is a projection pattern (d = projection name), is it?
        projs <- liftTCM $ mapMaybeM (\ d -> fmap (d,) <$> isProjection d) (toList ds)
        when (null projs) notProjP
        -- If the target is not a record type, that's an error.
        -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
        caseMaybeM (liftTCM $ isRecordType $ unArg b) notRecord $ \(r, vs, def) -> case def of
          Record{ recFields = fs } -> do
            reportSDoc "tc.lhs.split" 20 $ sep
              [ text $ "we are of record type r  = " ++ prettyShow r
              , text   "applied to parameters vs = " <+> prettyTCM vs
              , text $ "and have fields       fs = " ++ prettyShow fs
              ]
            let ai   = getArgInfo p
            -- Try the projection candidates.
            -- Fail hard for the last candidate.
            msum $ mapAwareLast (tryProj o ai fs r vs $ isAmbiguous ambD) projs
            -- -- This fails softly on all (if more than one) candidates.
            -- msum $ map (tryProj o ai fs r vs (length projs >= 2)) projs

          _ -> __IMPOSSIBLE__
      where
      failure   = liftTCM $ typeError $ CannotEliminateWithPattern p $ unArg b
      notProjP  = liftTCM $ typeError $ NotAProjectionPattern p
      notRecord = failure -- lift $ typeError $ ShouldBeRecordType $ unArg b
      wrongHiding :: MonadTCM tcm' => QName -> tcm' a
      wrongHiding d = typeError . GenericDocError =<< do
        liftTCM $ text "Wrong hiding used for projection " <+> prettyTCM d
      -- Issue #2423: error which reports the disambiguation
      wrongProj :: MonadTCM tcm' => QName -> Bool -> tcm' a
      wrongProj d amb = typeError . GenericDocError =<< do
        liftTCM $ sep
          [ text "Cannot eliminate type "
          , prettyTCM (unArg b)
          , text " with projection "
          , if amb then text . prettyShow =<< dropTopLevelModule d else prettyTCM d
          ]

      -- | Pass 'True' unless last element of the list.
      mapAwareLast :: forall a b. (Bool -> a -> b) -> [a] -> [b]
      mapAwareLast f []     = []
      mapAwareLast f [a]    = [f False a]
      mapAwareLast f (a:as) = f True a : mapAwareLast f as

      tryProj
        :: ProjOrigin           -- ^ Origin of projection pattern.
        -> ArgInfo              -- ^ ArgInfo of projection pattern.
        -> [Arg QName]          -- ^ Fields of record type under consideration.
        -> QName                -- ^ Name of record type we are eliminating.
        -> Args                 -- ^ Parameters of record type we are eliminating.
        -> Bool                 -- ^ Did we start out with an ambiguous projection in the beginning?
        -> Bool                 -- ^ More than 1 candidates?  If yes, fail softly.
        -> (QName, Projection)  -- ^ Current candidate.
        -> ListT tcm SplitProblem
      tryProj o ai fs r vs amb soft (d0, proj) = do
        -- Recoverable errors are those coming from the projection.
        -- If we have several projections we fail @soft@ly and just try the next one.
        let ambErr err = if soft then mzero else err
            ambTry m
             | soft = unlessM (liftTCM $ tryConversion m) mzero -- succeed without constraints
             -- This would leave constraints:
             -- -- | amb = whenNothingM (liftTCM $ tryMaybe $ disableDestructiveUpdate m) mzero
             | otherwise = liftTCM $ noConstraints m
        case proj of
          -- Andreas, 2015-05-06 issue 1413 projProper=Nothing is not impossible
          Projection{projProper = Nothing} -> ambErr notProjP
          Projection{projProper = Just qr, projOrig = d, projLams = lams} -> do
            let ai = projArgInfo proj
            -- If projIndex==0, then the projection is already applied
            -- to the record value (like in @open R r@), and then it
            -- is no longer a projection but a record field.
            when (null lams) $ ambErr notProjP
            liftTCM $ reportSLn "tc.lhs.split" 90 "we are a projection pattern"
            -- If the target is not a record type, that's an error.
            -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
            liftTCM $ reportSDoc "tc.lhs.split" 20 $ sep
              [ text $ "proj                  d0 = " ++ prettyShow d0
              , text $ "original proj         d  = " ++ prettyShow d
              ]
            -- Get the field decoration.
            -- If the projection pattern name @d@ is not a field name,
            -- we have to try the next projection name.
            -- If this was not an ambiguous projection, that's an error.
            argd <- maybe (ambErr $ wrongProj d amb) return $ List.find ((d ==) . unArg) fs
            let ai' = setRelevance (getRelevance argd) ai

            -- Andreas, 2016-12-31, issue #2374:
            -- We can also disambiguate by hiding info.
            unless (sameHiding p ai) $ ambErr $ wrongHiding d

            -- Andreas, 2016-12-31, issue #1976:
            -- Check parameters.
            ambTry $ checkParameters qr r vs

            -- From here, we have the correctly disambiguated projection.
            -- Thus, we no longer catch errors.

            -- For highlighting, we remember which name we disambiguated to.
            -- This is safe here (fingers crossed) as we won't decide on a
            -- different projection even if we backtrack and come here again.
            liftTCM $ storeDisambiguatedName d0

            -- Get the type of projection d applied to "self"
            dType <- liftTCM $ defType <$> getConstInfo d  -- full type!
            liftTCM $ reportSDoc "tc.lhs.split" 20 $ sep
              [ text "we are being projected by dType = " <+> prettyTCM dType
              ]
            -- This should succeed, as we have the correctly disambiguated.
            liftTCM $ SplitRest (Arg ai' d0) o <$> dType `piApplyM` vs

    -- if there are no more patterns left in the problem rest, there is nothing to split:
    splitRest _ _ = mzero

    -- | In @splitP aps tel@,
    --   @aps@ are the user patterns on which we are splitting (inPats),
    --   @tel@ records the types of @aps@.
    splitP :: [NamedArg A.Pattern]
           -> Telescope
           -> ListT tcm SplitProblem

    -- no more patterns?  pull them from the rest
    splitP []           _                      = splitRest pr b
    -- patterns but no more types? that's an error
    splitP (_:_)        EmptyTel               = __IMPOSSIBLE__
    -- (we can never have an ExtendTel without Abs)
    splitP _            (ExtendTel _ NoAbs{})  = __IMPOSSIBLE__

    -- pattern with type?  Let's get to work:
    splitP ps0@(p : ps) tel0@(ExtendTel dom@(Dom ai a) xtel@(Abs x tel)) = do

      liftTCM $ reportSDoc "tc.lhs.split" 30 $ sep
        [ text "splitP looking at pattern"
        , nest 2 $ text "p   =" <+> prettyA p
        , nest 2 $ text "dom =" <+> prettyTCM dom
        ]

      -- Andreas, 2016-06-30, issue #2075: need test here!
      unless (sameHiding p ai) $ typeError WrongHidingInLHS

      -- Possible reinvokations:
      let -- 1. Redo this argument (after meta instantiation).
          tryAgain = splitP ps0 tel0
          -- 2. Try to split on next argument.
          keepGoing = consSplitProblem p <$> do
            underAbstraction dom xtel $ \ tel -> splitP ps tel

      -- Tell when splitting is blocked by something
      let blockedOnMeta m = lift $ tell $ blocked m ()
          blockedOn nb    = lift $ tell $ NotBlocked nb ()

      p <- liftTCM $ expandLitPattern p
      case snd $ asView $ namedArg p of

        -- Case: projection pattern.  That's an error.
        A.ProjP{} -> typeError $
          CannotEliminateWithPattern p (telePi tel0 $ unArg b)

        -- Case: literal pattern.
        p@(A.LitP lit)  -> do
          -- Note that, in the presence of --without-K, this branch is
          -- based on the assumption that the types of literals are
          -- not indexed.

          -- Andreas, 2010-09-07 cannot split on irrelevant args
          when (unusableRelevance $ getRelevance ai) $
            typeError $ SplitOnIrrelevant p dom

          -- Succeed if the split type is (already) equal to the type of the literal.
          ifNotM (liftTCM $ tryConversion $ equalType a =<< litType lit)
            {- then -} keepGoing $
            {- else -} return Split
              { splitLPats   = empty
              , splitFocus   = Arg ai $ LitFocus lit qs a
              , splitRPats   = Problem ps __IMPOSSIBLE__
              }
              `mplus` keepGoing

        -- Case: record pattern
        p@(A.RecP _patInfo fs) -> do
          res <- liftTCM $ tryRecordType a
          case res of
            -- Subcase: blocked
            Left (Blocked m a') -> blockedOnMeta m >> keepGoing

            -- Subcase: not a record type or blocked on variable.
            Left (NotBlocked nb a') -> blockedOn nb >> keepGoing  -- If not record type, error will be given later.
              -- typeError . GenericDocError =<< do
              --   lift $ text "Record pattern at non-record type " <+> prettyTCM a'

            -- Subcase: a record type (d vs)
            Right (d, vs, def) -> do
              let np = recPars def
              let (pars, ixs) = splitAt np vs
              liftTCM $ reportSDoc "tc.lhs.split" 10 $ vcat
                [ sep [ text "splitting on"
                      , nest 2 $ fsep [ prettyA p, text ":", prettyTCM dom ]
                      ]
                , nest 2 $ text "pars =" <+> fsep (punctuate comma $ map prettyTCM pars)
                , nest 2 $ text "ixs  =" <+> fsep (punctuate comma $ map prettyTCM ixs)
                ]
              let c = killRange $ conName $ recConHead def
              let -- Field names with ArgInfo.
                  axs = recordFieldNames def

              -- In es omitted explicit fields are replaced by underscores
              -- (from missingExplicits). Omitted implicit or instance fields
              -- are still left out and inserted later by computeNeighborhood.
              args <- liftTCM $ insertMissingFields d (const $ A.WildP A.patNoRange) fs axs
              (return Split
                { splitLPats   = empty
                , splitFocus   = Arg ai $ Focus c ConORec args (getRange p) qs d pars ixs a
                , splitRPats   = Problem ps __IMPOSSIBLE__
                }) `mplus` keepGoing

        -- Case: absurd pattern.
        p@(A.AbsurdP info) -> do
          liftTCM $ reportSDoc "tc.lhs.split.absurd" 30 $ text "split AbsurdP: type is " <+> prettyTCM a
          let i = size tel
          (return Split
            { splitLPats = empty
            , splitFocus = Arg ai $ AbsurdFocus info i $ raise (i+1) a
            , splitRPats = Problem ps __IMPOSSIBLE__
            }) `mplus` keepGoing

        -- Case: constructor pattern.
        p@(A.ConP ci ambC args) -> do
          let tryInstantiate m a'
                | Just c <- getUnambiguous ambC = do
                  liftTCM $ reportSDoc "tc.lhs.split" 30 $
                    text "split ConP: type is blocked"
                    -- Type is blocked by a meta and constructor is unambiguous,
                    -- in this case try to instantiate the meta.
                  ok <- liftTCM $ do
                    Constructor{ conData = d } <- theDef <$> getConstInfo c
                    dt     <- defType <$> getConstInfo d
                    vs     <- newArgsMeta dt
                    Sort s <- ignoreSharing . unEl <$> reduce (piApply dt vs)
                    tryConversion $ equalType a' (El s $ Def d $ map Apply vs)
                  if ok then tryAgain else blockedOnMeta m >> keepGoing
                | otherwise = do
                  liftTCM $ reportSDoc "tc.lhs.split" 30 $
                    text "split ConP: type is blocked and constructor is ambiguous"
                  blockedOnMeta m
                  keepGoing
          -- ifBlockedType reduces the type
          ifBlockedType a tryInstantiate $ \ nb a' -> do
            liftTCM $ reportSDoc "tc.lhs.split" 30 $ text "split ConP: type is " <+> prettyTCM a'
            case ignoreSharing $ unEl a' of

              -- Subcase: split type is a Def.
              Def d es    -> (liftTCM $ theDef <$> getConstInfo d) >>= \case

               -- Issue #2253: the data type could be abstract.
               AbstractDefn{} -> liftTCM $ traceCall (CheckPattern p EmptyTel a) $ do
                 typeError . GenericDocError =<< do
                   text "Cannot split on abstract data type" <+> prettyTCM d

               def -> do

                -- We cannot split on (shape-)irrelevant non-records.
                -- Andreas, 2011-10-04 unless allowed by option
                liftTCM $ reportSLn "tc.lhs.split" 30 $ "split ConP: relevance is " ++ show ai
                unless (defIsRecord def) $
                  when (unusableRelevance $ getRelevance ai) $
                  unlessM (liftTCM $ optExperimentalIrrelevance <$> pragmaOptions) $
                  typeError $ SplitOnIrrelevant p dom

                -- Check that we are at record or data type and return
                -- the number of parameters.
                let mp = case def of
                          Datatype{dataPars = np} -> Just np
                          Record{recPars = np}    -> Just np
                          _                       -> Nothing
                case mp of
                  Nothing -> keepGoing
                  Just np -> do
                    let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                    traceCall (CheckPattern p EmptyTel a) $ do  -- TODO: wrong telescope
                      -- Check that we construct something in the right datatype
                      c <- liftTCM $ do
                          -- Andreas, 2017-08-13, issue #2686: ignore abstract constructors
                          (cs1, cs') <- unzip . snd . partitionEithers . toList <$> do
                            forM (unAmbQ ambC) $ \ c -> mapRight ((c,) . conName) <$> getConHead c
                          when (null cs1) $ typeError $ AbstractConstructorNotInScope $ headAmbQ ambC
                          d'  <- canonicalName d
                          cs0 <- (theDef <$> getConstInfo d') <&> \case
                                Datatype{dataCons = cs0} -> cs0
                                Record{recConHead = c0}  -> [conName c0]
                                _ -> __IMPOSSIBLE__
                          case [ c | (c, c') <- zip cs1 cs', elem c' cs0 ] of
                            [c]   -> do
                              -- If constructor pattern was ambiguous,
                              -- remember our choice for highlighting info.
                              when (isAmbiguous ambC) $ storeDisambiguatedName c
                              return c
                            []    -> typeError $ ConstructorPatternInWrongDatatype (head cs1) d
                            cs3   -> -- if there are more than one we give up (they might have different types)
                              typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d cs3

                      let (pars, ixs) = splitAt np vs
                      liftTCM $ reportSDoc "tc.lhs.split" 10 $ vcat
                        [ sep [ text "splitting on"
                              , nest 2 $ fsep [ prettyA p, text ":", prettyTCM dom ]
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
                      -- Andreas, 2016-12-31 fixing issue #1975
                      -- Do this also for constructors which were originally ambiguous.
                      checkConstructorParameters c d pars

                      (return Split
                        { splitLPats   = empty
                        , splitFocus   = Arg ai $ Focus c (A.patOrigin ci) args (getRange p) qs d pars ixs a
                        , splitRPats   = Problem ps __IMPOSSIBLE__
                        }) `mplus` keepGoing
              -- Subcase: split type is not a Def.
              _   -> blockedOn nb >> keepGoing

        -- Case: neither literal nor constructor pattern.
        _ -> keepGoing


-- | @checkConstructorParameters c d pars@ checks that the data/record type
--   behind @c@ is has initial parameters (coming e.g. from a module instantiation)
--   that coincide with an prefix of @pars@.
checkConstructorParameters :: MonadTCM tcm => QName -> QName -> Args -> tcm ()
checkConstructorParameters c d pars = do
  dc <- liftTCM $ getConstructorData c
  checkParameters dc d pars

-- | Check that given parameters match the parameters of the inferred
--   constructor/projection.
checkParameters
  :: MonadTCM tcm
  => QName  -- ^ The record/data type name of the chosen constructor/projection.
  -> QName  -- ^ The record/data type name as supplied by the type signature.
  -> Args   -- ^ The parameters.
  -> tcm ()
checkParameters dc d pars = liftTCM $ do
  a  <- reduce (Def dc [])
  case ignoreSharing a of
    Def d0 es -> do -- compare parameters
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reportSDoc "tc.lhs.split" 40 $
        vcat [ nest 2 $ text "d                   =" <+> (text . prettyShow) d
             , nest 2 $ text "d0 (should be == d) =" <+> (text . prettyShow) d0
             , nest 2 $ text "dc                  =" <+> (text . prettyShow) dc
             , nest 2 $ text "vs                  =" <+> prettyTCM vs
             ]
      -- when (d0 /= d) __IMPOSSIBLE__ -- d could have extra qualification
      t <- typeOfConst d
      compareArgs [] [] t (Def d []) vs (take (length vs) pars)
    _ -> __IMPOSSIBLE__
