{-# LANGUAGE PatternSynonyms #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class

import Agda.Syntax.Position (beginningOf, getRange)
import Agda.Syntax.Common
import Agda.Syntax.Abstract (Binder, mkBinder_)
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (unquoteTactic)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Tuple

-- Cut and paste from insertImplicitPatternsT:

-- | Insert implicit binders in a list of binders, but not at the end.
insertImplicitBindersT
  :: (PureTCM m, MonadError TCErr m, MonadFresh NameId m, MonadTrace m)
  => [NamedArg Binder]     -- ^ Should be non-empty, otherwise nothing happens.
  -> Type                  -- ^ Function type eliminated by arguments given by binders.
  -> m [NamedArg Binder] -- ^ Padded binders.
insertImplicitBindersT = \case
  []     -> \ _ -> return []
  b : bs -> List1.toList <.> insertImplicitBindersT1 (b :| bs)

-- | Insert implicit binders in a list of binders, but not at the end.
insertImplicitBindersT1
  :: (PureTCM m, MonadError TCErr m, MonadFresh NameId m, MonadTrace m)
  => List1 (NamedArg Binder)        -- ^ Non-empty.
  -> Type                           -- ^ Function type eliminated by arguments given by binders.
  -> m (List1 (NamedArg Binder))  -- ^ Padded binders.
insertImplicitBindersT1 bs@(b :| _) a = setCurrentRange b $ do
  TelV tel ty0 <- telViewUpTo' (-1) (not . visible) a
  reportSDoc "tc.term.lambda.imp" 20 $
    vcat [ "insertImplicitBindersT"
         , nest 2 $ "bs  = " <+> do
             brackets $ fsep $ punctuate comma $ fmap prettyA bs
         , nest 2 $ "tel = " <+> prettyTCM tel
         , nest 2 $ "ty  = " <+> addContext tel (prettyTCM ty0)
         ]
  reportSDoc "tc.term.lambda.imp" 70 $
    vcat [ "insertImplicitBindersT"
         , nest 2 $ "bs  = " <+> (text . show . List1.toList) bs
         , nest 2 $ "tel = " <+> (text . show) tel
         , nest 2 $ "ty  = " <+> (text . show) ty0
         ]
  hs <- insImp b tel
  -- Continue with implicit binders inserted before @b@.
  let bs0@(b1 :| bs1) = List1.prependList hs bs
  reduce a >>= piOrPath >>= \case
    -- If @a@ is a function (or path) type, continue inserting after @b1@.
    Left (_, ty) -> (b1 :|) <$> insertImplicitBindersT bs1 (absBody ty)
    -- Otherwise, we are done.
    Right{}      -> return bs0
  where
  insImp b EmptyTel = return []
  insImp b tel = case insertImplicit b $ telToList tel of
    BadImplicits   -> typeError WrongHidingInLHS
    NoSuchName x   -> typeError WrongHidingInLHS
    ImpInsert doms -> mapM implicitArg doms
      where
      implicitArg d = setOrigin Inserted . unnamedArg (domInfo d) . mkBinder_ <$> do
        freshNoName $ beginningOf $ getRange b

-- | @implicitArgs n expand t@ generates up to @n@ implicit argument
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding info of its domain.

implicitArgs
  :: (PureTCM m, MonadMetaSolver m, MonadTCM m)
  => Int               -- ^ @n@, the maximum number of implicts to be inserted.
  -> (Hiding -> Bool)  -- ^ @expand@, the predicate to test whether we should keep inserting.
  -> Type              -- ^ The (function) type @t@ we are eliminating.
  -> m (Args, Type)  -- ^ The eliminating arguments and the remaining type.
implicitArgs n expand t = mapFst (map (fmap namedThing)) <$> do
  implicitNamedArgs n (\ h x -> expand h) t

-- | @implicitNamedArgs n expand t@ generates up to @n@ named implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding and name info of its domain.

implicitNamedArgs
  :: (PureTCM m, MonadMetaSolver m, MonadTCM m)
  => Int                          -- ^ @n@, the maximum number of implicts to be inserted.
  -> (Hiding -> ArgName -> Bool)  -- ^ @expand@, the predicate to test whether we should keep inserting.
  -> Type                         -- ^ The (function) type @t@ we are eliminating.
  -> m (NamedArgs, Type)        -- ^ The eliminating arguments and the remaining type.
implicitNamedArgs 0 expand t0 = return ([], t0)
implicitNamedArgs n expand t0 = do
    t0' <- reduce t0
    reportSDoc "tc.term.args" 30 $ "implicitNamedArgs" <+> prettyTCM t0'
    reportSDoc "tc.term.args" 80 $ "implicitNamedArgs" <+> text (show t0')
    case unEl t0' of
      Pi dom@Dom{domInfo = info, domTactic = tac, unDom = a} b
        | let x = bareNameWithDefault "_" dom, expand (getHiding info) x -> do
          info' <- if hidden info then return info else do
            reportSDoc "tc.term.args.ifs" 15 $
              "inserting instance meta for type" <+> prettyTCM a
            reportSDoc "tc.term.args.ifs" 40 $ nest 2 $ vcat
              [ "x      = " <+> text (show x)
              , "hiding = " <+> text (show $ getHiding info)
              ]

            return $ makeInstance info
          (_, v) <- newMetaArg info' x CmpLeq a
          whenJust tac $ \ tac -> liftTCM $ unquoteTactic tac v a
          let narg = Arg info (Named (Just $ WithOrigin Inserted $ unranged x) v)
          mapFst (narg :) <$> implicitNamedArgs (n-1) expand (absApp b v)
      _ -> return ([], t0')

-- | Create a metavariable according to the 'Hiding' info.

newMetaArg
  :: (PureTCM m, MonadMetaSolver m)
  => ArgInfo    -- ^ Kind/relevance of meta.
  -> ArgName    -- ^ Name suggestion for meta.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the type.
  -> Type       -- ^ Type of meta.
  -> m (MetaId, Term)  -- ^ The created meta as id and as term.
newMetaArg info x cmp a = do
  prp <- runBlocked $ isPropM a
  let irrelevantIfProp =
        if prp == Right True
        then applyRelevanceToContext Irrelevant
        else id
  applyModalityToContext info $ irrelevantIfProp $
    newMeta (getHiding info) (argNameToString x) a
  where
    newMeta :: MonadMetaSolver m => Hiding -> String -> Type -> m (MetaId, Term)
    newMeta Instance{} n = newInstanceMeta n
    newMeta Hidden     n = newNamedValueMeta RunMetaOccursCheck n cmp
    newMeta NotHidden  n = newNamedValueMeta RunMetaOccursCheck n cmp

-- | Create a questionmark according to the 'Hiding' info.

newInteractionMetaArg
  :: ArgInfo    -- ^ Kind/relevance of meta.
  -> ArgName    -- ^ Name suggestion for meta.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the type.
  -> Type       -- ^ Type of meta.
  -> TCM (MetaId, Term)  -- ^ The created meta as id and as term.
newInteractionMetaArg info x cmp a = do
  applyModalityToContext info $
    newMeta (getHiding info) (argNameToString x) a
  where
    newMeta :: Hiding -> String -> Type -> TCM (MetaId, Term)
    newMeta Instance{} n = newInstanceMeta n
    newMeta Hidden     n = newNamedValueMeta' RunMetaOccursCheck n cmp
    newMeta NotHidden  n = newNamedValueMeta' RunMetaOccursCheck n cmp

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
