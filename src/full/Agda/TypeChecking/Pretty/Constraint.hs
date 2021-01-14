
module Agda.TypeChecking.Pretty.Constraint where

import Prelude hiding (null)

import qualified Data.Set as Set
import qualified Data.List as List
import Data.Function

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info     as A
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Errors

import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Impossible

prettyConstraint :: MonadPretty m => ProblemConstraint -> m Doc
prettyConstraint c = f (locallyTCState stInstantiateBlocking (const True) $ prettyTCM c)
  where
    r   = getRange c
    f :: MonadPretty m => m Doc -> m Doc
    f d = if null $ P.pretty r
          then d
          else d $$ nest 4 ("[ at" <+> prettyTCM r <+> "]")

interestingConstraint :: ProblemConstraint -> Bool
interestingConstraint pc = go $ clValue (theConstraint pc)
  where
    go UnBlock{} = False
    go _         = True

prettyInterestingConstraints :: MonadPretty m => [ProblemConstraint] -> m [Doc]
prettyInterestingConstraints cs = mapM (prettyConstraint . stripPids) $ List.sortBy (compare `on` isBlocked) cs'
  where
    isBlocked = not . null . allBlockingProblems . constraintUnblocker
    cs' = filter interestingConstraint cs
    interestingPids = Set.unions $ map (allBlockingProblems . constraintUnblocker) cs'
    stripPids (PConstr pids unblock c) = PConstr (Set.intersection pids interestingPids) unblock c

instance PrettyTCM ProblemConstraint where
  prettyTCM (PConstr pids unblock c) = prettyTCM c <?> parensNonEmpty (sep [blockedOn unblock, prPids (Set.toList pids)])
    where
      prPids []    = empty
      prPids [pid] = "belongs to problem" <+> prettyTCM pid
      prPids pids  = "belongs to problems" <+> fsep (punctuate "," $ map prettyTCM pids)

      comma | null pids = empty
            | otherwise = ","

      blockedOn (UnblockOnAll bs) | Set.null bs = empty
      blockedOn (UnblockOnAny bs) | Set.null bs = "stuck" <> comma
      blockedOn u = "blocked on" <+> (prettyTCM u <> comma)

instance PrettyTCM Constraint where
    prettyTCM = \case
        ValueCmp cmp ty s t -> prettyCmp (prettyTCM cmp) s t <?> prettyTCM ty
        ValueCmp_ cmp ty s t -> prettyCmp (prettyTCM cmp) s t <?> prettyTCM ty
        ValueCmpOnFace cmp p ty s t ->
            sep [ prettyTCM p <+> "|"
                , prettyCmp (prettyTCM cmp) s t ]
            <?> (":" <+> prettyTCMCtx TopCtx ty)
        ElimCmp cmps fs t v us vs -> prettyCmp "~~" us vs   <?> (":" <+> prettyTCMCtx TopCtx t)
        ElimCmp_ cmps fs t v us vs -> prettyCmp "~~" us vs   <?> (":" <+> prettyTCMCtx TopCtx t <+> "∋" <+> prettyTCMCtx TopCtx v)
        LevelCmp cmp a b         -> prettyCmp (prettyTCM cmp) a b
        SortCmp cmp s1 s2        -> prettyCmp (prettyTCM cmp) s1 s2
        UnBlock m   -> do
            -- BlockedConst t <- mvInstantiation <$> lookupMeta m
            mi <- mvInstantiation <$> lookupMeta m
            case mi of
              BlockedConst t -> prettyCmp ":=" m t
              PostponedTypeCheckingProblem cl -> enterClosure cl $ \p ->
                prettyCmp ":=" m p
              Open{}  -> __IMPOSSIBLE__
              OpenInstance{} -> __IMPOSSIBLE__
              InstV{} -> empty
              -- Andreas, 2017-01-11, issue #2637:
              -- The size solver instantiates some metas with infinity
              -- without cleaning up the UnBlock constraints.
              -- Thus, this case is not IMPOSSIBLE.
              --
              -- InstV args t -> do
              --   reportS "impossible" 10
              --     [ "UnBlock meta " ++ show m ++ " surprisingly has InstV instantiation:"
              --     , show m ++ show args ++ " := " ++ show t
              --     ]
              --   __IMPOSSIBLE__
        FindInstance m mcands -> do
            t <- getMetaType m
            sep [ "Resolve instance argument" <?> prettyCmp ":" m t
                , cands
                ]
          where
            cands =
              case mcands of
                Nothing -> "No candidates yet"
                Just cnds ->
                  hang "Candidates" 2 $ vcat
                    [ hang (overlap c <+> prettyTCM c <+> ":") 2 $
                            prettyTCM (candidateType c) | c <- cnds ]
              where overlap c | candidateOverlappable c = "overlap"
                              | otherwise               = empty
        IsEmpty r t ->
            "Is empty:" <?> prettyTCMCtx TopCtx t
        CheckSizeLtSat t ->
            "Is not empty type of sizes:" <?> prettyTCMCtx TopCtx t
        CheckFunDef d i q cs err -> do
            t <- defType <$> getConstInfo q
            vcat [ "Check definition of" <+> prettyTCM q <+> ":" <+> prettyTCM t
                 , nest 2 $ "stuck because" <?> prettyTCM err ]
        HasBiggerSort a -> "Has bigger sort:" <+> prettyTCM a
        HasPTSRule a b -> "Has PTS rule:" <+> case b of
          NoAbs _ b -> prettyTCM (a,b)
          Abs x b   -> "(" <> (prettyTCM a <+> "," <+> addContext x (prettyTCM b)) <> ")"
        UnquoteTactic v _ _ -> do
          e <- reify v
          prettyTCM (A.App A.defaultAppInfo_ (A.Unquote A.exprNoRange) (defaultNamedArg e))
        CheckMetaInst x -> do
          m <- lookupMeta x
          case mvJudgement m of
            HasType{ jMetaType = t } -> prettyTCM x <+> ":" <+> prettyTCM t
            IsSort{} -> prettyTCM x <+> "is a sort"
        CheckLockedVars t ty lk lk_ty -> do
          "Lock" <+> prettyTCM lk <+> "|-" <+> prettyTCMCtx TopCtx t <+> ":" <+> prettyTCM ty
        UsableAtModality mod t -> "Is usable at" <+> prettyTCM mod <+> ":" <+> prettyTCM t

      where
        prettyCmp
          :: (PrettyTCM a, PrettyTCM b, MonadPretty m)
          => m Doc -> a -> b -> m Doc
        prettyCmp cmp x y = prettyTCMCtx TopCtx x <?> (cmp <+> prettyTCMCtx TopCtx y)
