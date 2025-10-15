{-# LANGUAGE PatternSynonyms #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class

import Data.Bifunctor (first)

import Agda.Syntax.Position (HasRange, beginningOf, getRange)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Abstract (Binder, mkBinder_)
import Agda.Syntax.Info ( MetaKind (InstanceMeta, UnificationMeta) )
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (unquoteTactic)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Constraint ()  -- PrettyTCM Constraint instance only
import Agda.TypeChecking.Telescope

import Agda.Utils.Function (applyWhen, applyWhenJust)
import Agda.Utils.Functor
import qualified Agda.Utils.List as List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Tuple

import Agda.Utils.Impossible

-- Cut and paste from insertImplicitPatternsT:

-- | Split a given Pi 'Type' until you reach the given named argument,
-- returning the number of arguments skipped to reach the right plicity
-- and name.
splitImplicitBinderT :: HasRange a => NamedArg a -> Type -> TCM (Telescope, Type)
splitImplicitBinderT narg ty = do
  -- Split off any invisible arguments at the front (so if the first
  -- argument is visible, return tel = EmptyTel)
  TelV tel ty0 <- telViewUpTo' (-1) (not . visible) ty

  case tel of
    -- If we didn't lob off any arguments then we can use the original
    -- type and the empty telescope
    EmptyTel -> pure (EmptyTel, ty)

    -- Otherwise we try inserting implicit arguments.
    _ -> setCurrentRange narg case insertImplicit narg $ telToList tel of
      BadImplicits   -> typeError WrongHidingInLHS
      NoSuchName x   -> typeError WrongHidingInLHS
      ImpInsert doms ->
        let (here, there) = splitTelescopeAt (length doms) tel
        in pure (here, abstract there ty0)

-- | @implicitArgs n expand t@ generates up to @n@ implicit argument
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding info of its domain.

implicitArgs
  :: (PureTCM m, MonadMetaSolver m, MonadTCM m)
  => Int               -- ^ @n@, the maximum number of implicts to be inserted.
  -> (Hiding -> Bool)  -- ^ @expand@, the predicate to test whether we should keep inserting.
  -> Type              -- ^ The (function) type @t@ we are eliminating.
  -> m (Args, Type)    -- ^ The eliminating arguments and the remaining type.
implicitArgs n expand t = first (map (fmap namedThing)) <$> do
  implicitNamedArgs n (\ h _x -> expand h) t

-- | @implicitNamedArgs n expand t@ generates up to @n@ named implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding and name info of its domain.

implicitNamedArgs
  :: (PureTCM m, MonadMetaSolver m, MonadTCM m)
  => Int                          -- ^ @n@, the maximum number of implicts to be inserted.
  -> (Hiding -> ArgName -> Bool)  -- ^ @expand@, the predicate to test whether we should keep inserting.
  -> Type                         -- ^ The (function) type @t@ we are eliminating.
  -> m (NamedArgs, Type)          -- ^ The eliminating arguments and the remaining type.
implicitNamedArgs n expand t0 = do
  (ncas, t) <- implicitCheckedArgs n expand t0
  let (ns, cas) = List.unzipWith (\ (Named n ca) -> (n, ca)) ncas
  es <- liftTCM $ noHeadConstraints cas
  let nargs = zipWith (\ n (Arg ai v) -> Arg ai (Named n v)) ns (fromMaybe __IMPOSSIBLE__ $ allApplyElims es)
  return (nargs, t)

-- | Make sure there are no head constraints attached to the eliminations
-- and just return the eliminations.
noHeadConstraints :: [CheckedArg] -> TCM [Elim]
noHeadConstraints = mapM noHeadConstraint

noHeadConstraint :: CheckedArg -> TCM Elim
noHeadConstraint (CheckedArg elim _  Nothing) = return elim
noHeadConstraint (CheckedArg _ range Just{} ) = do
  setCurrentRange range do
    typeError $ NotSupported $
     "Lock constraints are not (yet) supported in this position."

-- | @implicitCheckedArgs n expand t@ generates up to @n@ named implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding and name info of its domain.

implicitCheckedArgs :: (PureTCM m, MonadMetaSolver m, MonadTCM m)
  => Int                          -- ^ @n@, the maximum number of implicts to be inserted.
  -> (Hiding -> ArgName -> Bool)  -- ^ @expand@, the predicate to test whether we should keep inserting.
  -> Type                         -- ^ The (function) type @t@ we are eliminating.
  -> m ([Named_ CheckedArg], Type)-- ^ The eliminating arguments and the remaining type.
implicitCheckedArgs 0 expand t0 = return ([], t0)
implicitCheckedArgs n expand t0 = do
    t0' <- reduce t0
    reportSDoc "tc.term.args" 30 $ "implicitCheckedArgs" <+> prettyTCM t0'
    reportSDoc "tc.term.args" 80 $ "implicitCheckedArgs" <+> text (show t0')
    case unEl t0' of
      Pi dom@Dom{domInfo = info, domTactic = mtac, unDom = a} b
        | let x = bareNameWithDefault "_" dom, expand (getHiding info) x -> do
          kind <- if hidden info then return UnificationMeta else do
            reportSDoc "tc.term.args.ifs" 15 $
              "inserting instance meta for type" <+> prettyTCM a
            reportSDoc "tc.term.args.ifs" 40 $ nest 2 $ vcat
              [ "x      = " <+> text (show x)
              , "hiding = " <+> text (show $ getHiding info)
              ]

            return InstanceMeta
          (_, v) <- newMetaArg kind info x CmpLeq a
          whenJust mtac \ tac -> liftTCM do
            applyModalityToContext info $ unquoteTactic tac v a
          let name = Just $ WithOrigin Inserted $ unranged x
          mc <- liftTCM $ makeLockConstraint t0' v
          let carg = CheckedArg{ caElim = Apply (Arg info v), caRange = empty, caConstraint = mc }
          first (Named name carg :) <$> implicitCheckedArgs (n-1) expand (absApp b v)
      _ -> return ([], t0')

-- | @makeLockConstraint u funType@(El _ (Pi (Dom{ domInfo=info, unDom=a }) _))@
--   creates a @CheckLockedVars@ constaint for lock @u : a@
--   if @getLock info == IsLock _@.
--
--   Precondition: 'Type' is reduced.
makeLockConstraint :: Type -> Term -> TCM (Maybe (Abs Constraint))
makeLockConstraint funType u =
  case funType of
    El _ (Pi (Dom{ domInfo = info, domName = dname, unDom = a }) _) -> do
      let
        x  = maybe "t" prettyShow dname
        mc = case getLock info of
          IsLock{} -> Just $ Abs x $
            CheckLockedVars (var 0) (raise 1 funType) (raise 1 $ Arg info u) (raise 1 a)
          IsNotLock -> Nothing
      whenJust mc \ c -> do
        reportSDoc "tc.term.lock" 40 do
          addContext (defaultDom $ funType) $ prettyTCM c
      return mc
    _ -> return Nothing

-- | Create a metavariable of 'MetaKind'.

newMetaArg
  :: (PureTCM m, MonadMetaSolver m)
  => MetaKind   -- ^ Kind of meta.
  -> ArgInfo    -- ^ Rrelevance of meta.
  -> ArgName    -- ^ Name suggestion for meta.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the type.
  -> Type       -- ^ Type of meta.
  -> m (MetaId, Term)  -- ^ The created meta as id and as term.
newMetaArg kind info x cmp a = do
  prp <- runBlocked $ isPropM a
  let irrelevantIfProp =
        applyWhen (prp == Right True) $ applyRelevanceToContext irrelevant
  applyModalityToContext info $ irrelevantIfProp $
    newMeta (argNameToString x) kind a
  where
    newMeta :: MonadMetaSolver m => String -> MetaKind -> Type -> m (MetaId, Term)
    newMeta n = \case
      InstanceMeta    -> newInstanceMeta n
      UnificationMeta -> newNamedValueMeta RunMetaOccursCheck n cmp

-- | Create a questionmark (always 'UnificationMeta').

newInteractionMetaArg
  :: ArgInfo    -- ^ Relevance of meta.
  -> ArgName    -- ^ Name suggestion for meta.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the type.
  -> Type       -- ^ Type of meta.
  -> TCM (MetaId, Term)  -- ^ The created meta as id and as term.
newInteractionMetaArg info x cmp a = do
  applyModalityToContext info $
    newNamedValueMeta' RunMetaOccursCheck (argNameToString x) cmp a

---------------------------------------------------------------------------

-- | Possible results of 'insertImplicit'.
data ImplicitInsertion
      = ImpInsert [Dom ()] -- ^ Success: this many implicits have to be inserted (list can be empty).
      | BadImplicits       -- ^ Error: hidden argument where there should have been a non-hidden argument.
      | NoSuchName ArgName -- ^ Error: bad named argument.
  deriving (Show)

pattern NoInsertNeeded :: ImplicitInsertion
pattern NoInsertNeeded = ImpInsert []

-- | If the next given argument is @a@ and the expected arguments are @ts@
--   @insertImplicit' a ts@ returns the prefix of @ts@ that precedes @a@.
--
--   If @a@ is named but this name does not appear in @ts@, the 'NoSuchName' exception is thrown.
--
insertImplicit
  :: NamedArg e  -- ^ Next given argument @a@.
  -> [Dom a]     -- ^ Expected arguments @ts@.
  -> ImplicitInsertion
insertImplicit a doms = insertImplicit' a $
  for doms $ \ dom ->
    dom $> bareNameWithDefault "_" dom

-- | If the next given argument is @a@ and the expected arguments are @ts@
--   @insertImplicit' a ts@ returns the prefix of @ts@ that precedes @a@.
--
--   If @a@ is named but this name does not appear in @ts@, the 'NoSuchName' exception is thrown.
--
insertImplicit'
  :: NamedArg e     -- ^ Next given argument @a@.
  -> [Dom ArgName]  -- ^ Expected arguments @ts@.
  -> ImplicitInsertion
insertImplicit' _ [] = BadImplicits
insertImplicit' a ts

  -- If @a@ is visible, then take the non-visible prefix of @ts@.
  | visible a = ImpInsert $ takeWhile notVisible $ map void ts

  -- If @a@ is named, take prefix of @ts@ until the name of @a@ (with correct hiding).
  -- If the name is not found, throw exception 'NoSuchName'.
  | Just x <- bareNameOf a = maybe (NoSuchName x) ImpInsert $
      takeHiddenUntil (\ t -> x == unDom t && sameHiding a t) ts

  -- If @a@ is neither visible nor named, take prefix of @ts@ with different hiding than @a@.
  | otherwise = maybe BadImplicits ImpInsert $
      takeHiddenUntil (sameHiding a) ts

    where
    -- @takeHiddenUntil p ts@ returns the 'getHiding' of the prefix of @ts@
    -- until @p@ holds or a visible argument is encountered.
    -- If @p@ never holds, 'Nothing' is returned.
    --
    --   Precondition: @p@ should imply @not . visible@.
    takeHiddenUntil :: (Dom ArgName -> Bool) -> [Dom ArgName] -> Maybe [Dom ()]
    takeHiddenUntil p ts =
      case ts2 of
        []      -> Nothing  -- Predicate was never true
        (t : _) -> if visible t then Nothing else Just $ map void ts1
      where
      (ts1, ts2) = break (\ t -> p t || visible t) ts
