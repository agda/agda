{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Rules.LHS.Split
  ( splitProblem
  ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe

import Data.Maybe (fromMaybe)
import Data.List hiding (null)
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

import Agda.Utils.Except (catchError)
import Agda.Utils.Functor ((<.>))
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Tuple
import qualified Agda.Utils.Pretty as P

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

splitProblem ::
  Maybe QName -- ^ The definition we are checking at the moment.
  -> Problem  -- ^ The current state of the lhs patterns.
  -> ListT TCM SplitProblem
splitProblem mf (Problem ps qs tel pr) = do
  lift $ do
    reportSLn "tc.lhs.split" 20 $ "initiating splitting"
      ++ maybe "" ((" for definition " ++) . show) mf
    reportSDoc "tc.lhs.split" 30 $ sep
      [ nest 2 $ text "ps   =" <+> sep (map (P.parens <.> prettyA) ps)
      , nest 2 $ text "qs   =" <+> sep (map (P.parens <.> prettyTCM . namedArg) qs)
      , nest 2 $ text "tel  =" <+> prettyTCM tel
      ]
  splitP ps tel
  where
    -- Result splitting
    splitRest :: ProblemRest -> ListT TCM SplitProblem
    splitRest (ProblemRest (p : ps) b) | Just f <- mf = do
      lift $ reportSDoc "tc.lhs.split" 20 $ sep
        [ text "splitting problem rest"
        , nest 2 $ text "pattern         p =" <+> prettyA p
        , nest 2 $ text "eliminates type b =" <+> prettyTCM b
        ]
      lift $ reportSDoc "tc.lhs.split" 80 $ sep
        [ nest 2 $ text $ "pattern (raw)   p = " ++ show p
        ]
      -- If the pattern is not a projection pattern, that's an error.
      -- Probably then there were too many arguments.
      caseMaybe (maybePostfixProjP p) failure $ \ (o, AmbQ ds) -> do
        -- So it is a projection pattern (d = projection name), is it?
        projs <- lift $ mapMaybeM (\ d -> fmap (d,) <$> isProjection d) ds
        when (null projs) notProjP
        -- If the target is not a record type, that's an error.
        -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
        caseMaybeM (lift $ isRecordType $ unArg b) notRecord $ \(r, vs, def) -> case def of
          Record{ recFields = fs } -> do
            lift $ reportSDoc "tc.lhs.split" 20 $ sep
              [ text $ "we are of record type r  = " ++ show r
              , text   "applied to parameters vs = " <+> prettyTCM vs
              , text $ "and have fields       fs = " ++ show fs
              ]
            -- The record "self" is the definition f applied to the patterns
            let es = patternsToElims qs
            -- Note: the module parameters are already part of qs
            let self = defaultArg $ Def f [] `applyE` es
            -- Try the projection candidates
            msum $ map (tryProj o self fs vs (length projs >= 2)) projs

          _ -> __IMPOSSIBLE__
      where
      failure   = lift $ typeError $ CannotEliminateWithPattern p $ unArg b
      notProjP  = lift $ typeError $ NotAProjectionPattern p
      notRecord = failure -- lift $ typeError $ ShouldBeRecordType $ unArg b
      wrongHiding :: MonadTCM tcm => QName -> tcm a
      wrongHiding d = typeError . GenericDocError =<< do
        liftTCM $ text "Wrong hiding used for projection " <+> prettyTCM d

      tryProj :: ProjOrigin -> Arg Term -> [Arg QName] -> Args -> Bool -> (QName, Projection) -> ListT TCM SplitProblem
      tryProj o self fs vs amb (d0, proj) = do
        -- Recoverable errors are those coming from the projection.
        -- If we have several projections (amb) we just try the next one.
        let ambErr err = if amb then mzero else err
        case proj of
          -- Andreas, 2015-05-06 issue 1413 projProper=Nothing is not impossible
          Projection{projProper = False} -> ambErr notProjP
          Projection{projProper = True, projOrig = d, projLams = lams} -> do
            let ai = projArgInfo proj
            -- If projIndex==0, then the projection is already applied
            -- to the record value (like in @open R r@), and then it
            -- is no longer a projection but a record field.
            when (null lams) $ ambErr notProjP
            lift $ reportSLn "tc.lhs.split" 90 "we are a projection pattern"
            -- If the target is not a record type, that's an error.
            -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
            lift $ reportSDoc "tc.lhs.split" 20 $ sep
              [ text $ "original proj         d  = " ++ show d
              ]
            -- Get the field decoration.
            -- If the projection pattern name @d@ is not a field name,
            -- we have to try the next projection name.
            -- If this was not an ambiguous projection, that's an error.
            argd <- maybe (ambErr failure) return $ find ((d ==) . unArg) fs

            -- From here, we have the correctly disambiguated projection.
            -- Thus, we no longer catch errors.
            unless (getHiding p == getHiding ai) $ wrongHiding d

            -- For highlighting, we remember which name we disambiguated to.
            -- This is safe here (fingers crossed) as we won't decide on a
            -- different projection even if we backtrack and come here again.
            lift $ storeDisambiguatedName d0

            -- Get the type of projection d applied to "self"
            dType <- lift $ defType <$> getConstInfo d  -- full type!
            lift $ reportSDoc "tc.lhs.split" 20 $ sep
              [ text "we are              self = " <+> prettyTCM (unArg self)
              , text "being projected by dType = " <+> prettyTCM dType
              ]
            -- This should succeed, as we have the correctly disambiguated.
            lift $ SplitRest argd o <$> dType `piApplyM` (vs ++ [self])

    -- if there are no more patterns left in the problem rest, there is nothing to split:
    splitRest _ = mzero

    -- | In @splitP aps iqs tel@,
    --   @aps@ are the user patterns on which we are splitting (inPats),
    --   @ips@ are the one-hole patterns of the current split state (outPats)
    --   in one-to-one correspondence with the pattern variables
    --   recorded in @tel@.
    splitP :: [NamedArg A.Pattern]
           -> Telescope
           -> ListT TCM SplitProblem

    -- no more patterns?  pull them from the rest
    splitP []           _                      = splitRest pr
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
      unless (getHiding p == getHiding ai) $ typeError WrongHidingInLHS

      -- Possible reinvokations:
      let -- 1. Redo this argument (after meta instantiation).
          tryAgain = splitP ps0 tel0
          -- 2. Try to split on next argument.
          keepGoing = consSplitProblem p x dom <$> do
            underAbstraction dom xtel $ \ tel -> splitP ps tel

      p <- lift $ expandLitPattern p
      case snd $ asView $ namedArg p of

        -- Case: projection pattern.  That's an error.
        A.ProjP{} -> typeError $
          CannotEliminateWithPattern p (telePi tel0 $ unArg $ restType pr)

        -- Case: literal pattern.
        p@(A.LitP lit)  -> do
          -- Note that, in the presence of --without-K, this branch is
          -- based on the assumption that the types of literals are
          -- not indexed.

          -- Andreas, 2010-09-07 cannot split on irrelevant args
          when (unusableRelevance $ getRelevance ai) $
            typeError $ SplitOnIrrelevant p dom

          -- Succeed if the split type is (already) equal to the type of the literal.
          ifNotM (lift $ tryConversion $ equalType a =<< litType lit)
            {- then -} keepGoing $
            {- else -} return Split
              { splitLPats   = empty
              , splitFocus   = Arg ai $ LitFocus lit qs a
              , splitRPats   = Abs x  $ Problem ps () tel __IMPOSSIBLE__
              }
              `mplus` keepGoing

        -- Case: record pattern
        p@(A.RecP _patInfo fs) -> do
          res <- lift $ tryRecordType a
          case res of
            -- Subcase: blocked
            Left Nothing -> keepGoing

            -- Subcase: not a record type or blocked on variable.
            Left (Just a') -> keepGoing  -- If not record type, error will be given later.
              -- typeError . GenericDocError =<< do
              --   lift $ text "Record pattern at non-record type " <+> prettyTCM a'

            -- Subcase: a record type (d vs)
            Right (d, vs, def) -> do
              let np = recPars def
              let (pars, ixs) = genericSplitAt np vs
              lift $ reportSDoc "tc.lhs.split" 10 $ vcat
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
              args <- lift $ insertMissingFields d (const $ A.WildP A.patNoRange) fs axs
              (return Split
                { splitLPats   = empty
                , splitFocus   = Arg ai $ Focus c ConPRec args (getRange p) qs d pars ixs a
                , splitRPats   = Abs x  $ Problem ps () tel __IMPOSSIBLE__
                }) `mplus` keepGoing

        -- Case: constructor pattern.
        p@(A.ConP ci (A.AmbQ cs) args) -> do
          let tryInstantiate a'
                | [c] <- cs = do
                    -- Type is blocked by a meta and constructor is unambiguous,
                    -- in this case try to instantiate the meta.
                  ok <- lift $ do
                    Constructor{ conData = d } <- theDef <$> getConstInfo c
                    dt     <- defType <$> getConstInfo d
                    vs     <- newArgsMeta dt
                    Sort s <- ignoreSharing . unEl <$> reduce (piApply dt vs)
                    tryConversion $ equalType a' (El s $ Def d $ map Apply vs)
                  if ok then tryAgain else keepGoing
                | otherwise = keepGoing
          -- ifBlockedType reduces the type
          ifBlockedType a (const tryInstantiate) $ \ a' -> do
            case ignoreSharing $ unEl a' of

              -- Subcase: split type is a Def.
              Def d es    -> do

                def <- liftTCM $ theDef <$> getConstInfo d

                -- We cannot split on (shape-)irrelevant non-records.
                -- Andreas, 2011-10-04 unless allowed by option
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
                      c <- lift $ do
                          cs' <- mapM canonicalName cs
                          d'  <- canonicalName d
                          let cons def = case theDef def of
                                Datatype{dataCons = cs} -> cs
                                Record{recConHead = c}      -> [conName c]
                                _                       -> __IMPOSSIBLE__
                          cs0 <- cons <$> getConstInfo d'
                          case [ c | (c, c') <- zip cs cs', elem c' cs0 ] of
                            [c]   -> do
                              -- If constructor pattern was ambiguous,
                              -- remember our choice for highlighting info.
                              when (length cs >= 2) $ storeDisambiguatedName c
                              return c
                            []    -> typeError $ ConstructorPatternInWrongDatatype (head cs) d
                            cs    -> -- if there are more than one we give up (they might have different types)
                              typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d cs

                      let (pars, ixs) = genericSplitAt np vs
                      lift $ reportSDoc "tc.lhs.split" 10 $ vcat
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
                      checkParsIfUnambiguous cs d pars

                      (return Split
                        { splitLPats   = empty
                        , splitFocus   = Arg ai $ Focus c (A.patOrigin ci) args (getRange p) qs d pars ixs a
                        , splitRPats   = Abs x  $ Problem ps () tel __IMPOSSIBLE__
                        }) `mplus` keepGoing
              -- Subcase: split type is not a Def.
              _   -> keepGoing

        -- Case: neither literal nor constructor pattern.
        _ -> keepGoing


-- | @checkParsIfUnambiguous [c] d pars@ checks that the data/record type
--   behind @c@ is has initial parameters (coming e.g. from a module instantiation)
--   that coincide with an prefix of @pars@.
checkParsIfUnambiguous :: MonadTCM tcm => [QName] -> QName -> Args -> tcm ()
checkParsIfUnambiguous [c] d pars = liftTCM $ do
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
