{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Records where

import Prelude hiding (null)

import Control.Applicative        ( (<|>) )
import Control.Monad.Except       ( MonadError )
import Control.Monad.Trans.Maybe  ( MaybeT(MaybeT), runMaybeT )
import Control.Monad.Writer       ( Writer, runWriter, tell )

import Data.Bifunctor
import qualified Data.List as List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Concrete (FieldAssignment'(..))
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal.MetaVars (unblockOnAnyMetaIn)
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (isNameInScope)

import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Base.Warning as W
import Agda.TypeChecking.Pretty as TCM
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad () --instance only
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import {-# SOURCE #-} Agda.TypeChecking.Primitive.Cubical.Base (isCubicalSubtype)
import {-# SOURCE #-} Agda.TypeChecking.ProjectionLike (eligibleForProjectionLike)

import Agda.Utils.Empty
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor (for, ($>), (<&>))
import Agda.Utils.Lens
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Tools to build record values

mkCon :: ConHead -> ConInfo -> Args -> Term
mkCon h info args = Con h info (map Apply args)

-- | Order the fields of a record construction.
orderFields
  :: forall a . HasRange a
  => ConOrigin         -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName             -- ^ Name of record type (for error message).
  -> (Arg C.Name -> a) -- ^ How to fill a missing field.
  -> [Arg C.Name]      -- ^ Field names of the record type.
  -> [(C.Name, a)]     -- ^ Provided fields with content in the record expression.
  -> Writer [RecordFieldWarning] [a]           -- ^ Content arranged in official order.
orderFields orig r fill axs fs = do
  -- reportSDoc "tc.record" 30 $ vcat
  --   [ "orderFields"
  --   , "  official fields: " <+> sep (map pretty xs)
  --   , "  provided fields: " <+> sep (map pretty ys)
  --   ]
  unless (orig == ConORecWhere) $
    List1.unlessNull alien     $ warn $ W.TooManyFields r missing

  List1.unlessNull duplicate $ warn $ W.DuplicateFields . fmap (fmap pure)
  return $ for axs $ \ ax -> fromMaybe (fill ax) $ lookup (unArg ax) uniq
  where
    (uniq, duplicate) = nubAndDuplicatesOn fst fs   -- separating duplicate fields
    xs        = map unArg axs                       -- official fields (accord. record type)
    missing   = filter (not . hasElem (map fst fs)) xs  -- missing  fields
    alien     = filter (not . hasElem xs . fst) fs      -- spurious fields
    warn w    = tell . singleton . w . fmap (second getRange)

-- | Raise generated 'RecordFieldWarning's as warnings.
warnOnRecordFieldWarnings :: Writer [RecordFieldWarning] a -> TCM a
warnOnRecordFieldWarnings comp = do
  let (res, ws) = runWriter comp
  mapM_ (warning . RecordFieldWarning) ws
  return res

-- | Raise generated 'RecordFieldWarning's as errors.
failOnRecordFieldWarnings :: Writer [RecordFieldWarning] a -> TCM a
failOnRecordFieldWarnings comp = do
  let (res, ws) = runWriter comp
  mapM_ (typeError . recordFieldWarningToError) ws
    -- This will raise the first warning (if any) as error.
  return res

-- | Order the fields of a record construction.
--   Raise generated 'RecordFieldWarning's as warnings.
orderFieldsWarn
  :: forall a . HasRange a
  => ConOrigin         -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName             -- ^ Name of record type (for error message).
  -> (Arg C.Name -> a) -- ^ How to fill a missing field.
  -> [Arg C.Name]      -- ^ Field names of the record type.
  -> [(C.Name, a)]     -- ^ Provided fields with content in the record expression.
  -> TCM [a]           -- ^ Content arranged in official order.
orderFieldsWarn o r fill axs fs = warnOnRecordFieldWarnings $ orderFields o r fill axs fs

-- | Order the fields of a record construction.
--   Raise generated 'RecordFieldWarning's as errors.
orderFieldsFail
  :: forall a . HasRange a
  => ConOrigin         -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName             -- ^ Name of record type (for error message).
  -> (Arg C.Name -> a) -- ^ How to fill a missing field.
  -> [Arg C.Name]      -- ^ Field names of the record type.
  -> [(C.Name, a)]     -- ^ Provided fields with content in the record expression.
  -> TCM [a]           -- ^ Content arranged in official order.
orderFieldsFail o r fill axs fs = failOnRecordFieldWarnings $ orderFields o r fill axs fs

-- | A record field assignment @record{xs = es}@ might not mention all
--   visible fields.  @insertMissingFields@ inserts placeholders for
--   the missing visible fields and returns the values in order
--   of the fields in the record declaration.
insertMissingFields
  :: forall a . HasRange a
  => ConOrigin            -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName                -- ^ Name of record type (for error reporting).
  -> (C.Name -> a)        -- ^ Function to generate a placeholder for missing visible field.
  -> [FieldAssignment' a] -- ^ Given fields.
  -> [Arg C.Name]         -- ^ All record field names with 'ArgInfo'.
  -> Writer [RecordFieldWarning] [NamedArg a]
       -- ^ Given fields enriched by placeholders for missing explicit fields.
insertMissingFields o r placeholder fs axs = do
  -- Compute the list of given fields, decorated with the ArgInfo from the record def.
  let arg x e = caseMaybe (List.find ((x ==) . unArg) axs) (defaultNamedArg e) $ \ a ->
        nameIfHidden a e <$ a
      givenFields = [ (x, Just $ arg x e) | FieldAssignment x e <- fs ]

  -- Omitted explicit fields are filled in with placeholders.
  -- Omitted implicit or instance fields
  -- are still left out and inserted later by checkArguments_.
  catMaybes <$> orderFields o r fill axs givenFields
  where
    fill :: Arg C.Name -> Maybe (NamedArg a)
    fill ax
      | visible ax = Just $ setOrigin Inserted $ unnamed . placeholder <$> ax
      | otherwise  = Nothing
    -- Andreas, 2017-04-13, issue #2494
    -- We need to put the field names as argument names for hidden arguments.
    -- Otherwise, insertImplicit does not do the right thing.
    nameIfHidden :: Arg C.Name -> c -> Named_ c
    nameIfHidden ax
      | visible ax = unnamed
      | otherwise  = named $ WithOrigin Inserted $ Ranged (getRange ax) $ prettyShow $ unArg ax

-- | A record field assignment @record{xs = es}@ might not mention all
--   visible fields.  @insertMissingFields@ inserts placeholders for
--   the missing visible fields and returns the values in order
--   of the fields in the record declaration.
insertMissingFieldsWarn
  :: forall a . HasRange a
  => ConOrigin            -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName                -- ^ Name of record type (for error reporting).
  -> (C.Name -> a)        -- ^ Function to generate a placeholder for missing visible field.
  -> [FieldAssignment' a] -- ^ Given fields.
  -> [Arg C.Name]         -- ^ All record field names with 'ArgInfo'.
  -> TCM [NamedArg a]     -- ^ Given fields enriched by placeholders for missing explicit fields.
insertMissingFieldsWarn o r placeholder fs axs =
  warnOnRecordFieldWarnings $ insertMissingFields o r placeholder fs axs

-- | A record field assignment @record{xs = es}@ might not mention all
--   visible fields.  @insertMissingFields@ inserts placeholders for
--   the missing visible fields and returns the values in order
--   of the fields in the record declaration.
insertMissingFieldsFail
  :: forall a . HasRange a
  => ConOrigin            -- ^ Indicates whether this is a @record@ or @record where@ expression.
  -> QName                -- ^ Name of record type (for error reporting).
  -> (C.Name -> a)        -- ^ Function to generate a placeholder for missing visible field.
  -> [FieldAssignment' a] -- ^ Given fields.
  -> [Arg C.Name]         -- ^ All record field names with 'ArgInfo'.
  -> TCM [NamedArg a]     -- ^ Given fields enriched by placeholders for missing explicit fields.
insertMissingFieldsFail o r placeholder fs axs =
  failOnRecordFieldWarnings $ insertMissingFields o r placeholder fs axs

---------------------------------------------------------------------------
-- * Query information about records from signature

-- | Check if a name refers to a record.
--   If yes, return record definition.
{-# SPECIALIZE isRecord :: QName -> TCM (Maybe RecordData) #-}
{-# SPECIALIZE isRecord :: QName -> ReduceM (Maybe RecordData) #-}
isRecord :: HasConstInfo m => QName -> m (Maybe RecordData)
isRecord r = do
  getConstInfo r <&> theDef <&> \case
    RecordDefn rd -> Just rd
    _ -> Nothing

-- | Get the definition for a record. Throws an exception if the name
--   does not refer to a record or the record is abstract.
getRecordDef :: (HasConstInfo m, ReadTCState m, MonadError TCErr m) => QName -> m RecordData
getRecordDef r = fromMaybeM err $ isRecord r
  where err = typeError $ ShouldBeRecordType (El __DUMMY_SORT__ $ Def r [])

-- | Get the record name belonging to a field name.
getRecordOfField :: QName -> TCM (Maybe QName)
getRecordOfField d = caseMaybeM (isProjection d) (return Nothing) $
  \ Projection{ projProper = proper, projFromType = r} ->
    return $ unArg r <$ proper -- if proper then Just (unArg r) else Nothing

-- | Get the field names of a record.
getRecordFieldNames :: (HasConstInfo m, ReadTCState m, MonadError TCErr m)
  => QName
  -> m [Dom C.Name]
getRecordFieldNames r = recordFieldNames <$> getRecordDef r

recordFieldNames :: RecordData -> [Dom C.Name]
recordFieldNames = map (fmap (nameConcrete . qnameName)) . _recFields

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs  <- HMap.elems <$> useTC (stSignature . sigDefinitions)
  idefs <- HMap.elems <$> useTC (stImports   . sigDefinitions)
  scope <- getScope
  return $ filter (`isNameInScope` scope) $ cands defs ++ cands idefs
  where
    cands defs = [ defName d | d <- defs, possible d ]
    possible def =
      -- Check whether the given fields are contained
      -- in the fields of record @def@ (if it is a record).
      case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given $
          Set.fromList $ map (nameConcrete . qnameName . unDom) fs
        _ -> False
    given = Set.fromList fields

-- | Get the field names belonging to a record type.
getRecordTypeFields
  :: Type  -- ^ Record type.  Need not be reduced.
  -> TCM [Dom QName]
getRecordTypeFields t = do
  t <- reduce t  -- Andreas, 2018-03-03, fix for #2989.
  case unEl t of
    Def r _ -> do
      rDef <- theDef <$> getConstInfo r
      case rDef of
        Record { recFields = fields } -> return fields
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

-- | Returns the given record type's constructor name (with an empty
-- range).
getRecordConstructor :: (HasConstInfo m, ReadTCState m, MonadError TCErr m) => QName -> m ConHead
getRecordConstructor r = killRange . _recConHead <$> getRecordDef r

-- | Reduce a type and check whether it is a record type.
--   Succeeds only if type is not blocked by a meta var.
--   If yes, return its name, parameters, and definition.
isRecordType :: PureTCM m => Type -> m (Maybe (QName, Args, RecordData))
isRecordType t = either (const Nothing) Just <$> tryRecordType t

-- | Reduce a type and check whether it is a record type.
--   Succeeds only if type is not blocked by a meta var.
--   If yes, return its name, parameters, and definition.
--   If no, return the reduced type (unless it is blocked).
tryRecordType :: PureTCM m => Type -> m (Either (Blocked Type) (QName, Args, RecordData))
tryRecordType t = ifBlocked t (\ m a -> return $ Left $ Blocked m a) $ \ nb t -> do
  let no = return $ Left $ NotBlocked nb t
  case unEl t of
    Def r es -> do
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      caseMaybeM (isRecord r) no $ \ def -> return $ Right (r,vs,def)
    _ -> no

-- | Get the original projection info for name.
{-# SPECIALIZE origProjection :: QName -> TCM (QName, Definition, Maybe Projection) #-}
origProjection ::  HasConstInfo m => QName -> m (QName, Definition, Maybe Projection)
origProjection f = do
  def <- getConstInfo f
  let proj     = isProjection_ $ theDef def
      fallback = return (f, def, proj)
  caseMaybe proj fallback $
    \ p@Projection{ projProper = proper, projOrig = f' } ->
      if isNothing proper || f == f' then fallback else do
        def <- getConstInfo f'
        return (f', def, isProjection_ $ theDef def)

-- | @getDefType f t@ computes the type of (possibly projection-(like))
--   function @f@ whose first argument has type @t@.
--   The `parameters' for @f@ are extracted from @t@.
--   @Nothing@ if @f@ is projection(like) but
--   @t@ is not a data/record/axiom type.
--
--   Precondition: @t@ is reduced.
--
--   See also: 'Agda.TypeChecking.Datatypes.getConType'
getDefType :: PureTCM m => QName -> Type -> m (Maybe Type)
getDefType f t = do
  -- Andreas, Issue #1973: we need to take the original projection
  -- since the parameters from the reduced type t are correct for
  -- the original projection only.
  -- Due to module application, the given (non-original) projection f
  -- may expect less parameters, those corresponding to a unreduced
  -- version of t (which we cannot obtain here).
  (f, def, mp) <- origProjection f
  let a = defType def
  -- if @f@ is not a projection (like) function, @a@ is the correct type
      fallback = return $ Just a
  reportSDoc "tc.deftype" 20 $ vcat
    [ "definition f =" <+> prettyTCM f <+> text ("  -- raw: " ++ prettyShow f)
    , "has type   a =" <+> prettyTCM a
    , "principal  t =" <+> prettyTCM t
    ]
  caseMaybe mp fallback $
    \ (Projection{ projIndex = n }) -> if n <= 0 then fallback else do
      -- otherwise, we have to instantiate @a@ to the "parameters" of @f@
      let npars | n == 0    = __IMPOSSIBLE__
                | otherwise = n - 1
      reportSLn "tc.deftype" 20 $ "projIndex    = " ++ show n
      -- we get the parameters from type @t@
      case unEl t of
        Def d es -> do
          -- Andreas, 2013-10-22
          -- we need to check this @Def@ is fully reduced.
          -- If it is stuck due to disabled reductions
          -- (because of failed termination check),
          -- we will produce garbage parameters.
          ifNotM (eligibleForProjectionLike d) failNotElig $ {- else -} do
            -- now we know it is reduced, we can safely take the parameters
            let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take npars es
            reportSDoc "tc.deftype" 20 $ vcat
              [ text $ "head d     = " ++ prettyShow d
              , "parameters =" <+> sep (map prettyTCM pars)
              ]
            reportSDoc "tc.deftype" 60 $ "parameters = " <+> pretty pars
            if length pars < npars then failure "does not supply enough parameters"
            else Just <$> a `piApplyM` pars
        _ -> failNotDef
  where
    failNotElig = failure "is not eligible for projection-likeness"
    failNotDef  = failure "is not a Def."
    failure reason = do
      reportSDoc "tc.deftype" 25 $ sep
        [ "Def. " <+> prettyTCM f <+> " is projection(like)"
        , "but the type "
        , prettyTCM t
        , text $ "of its argument " ++ reason
        ]
      reportSDoc "tc.deftype" 60 $ "raw type: " <+> pretty t
      return $ case unEl t of
        Dummy{} -> Just __DUMMY_TYPE__
        _       -> Nothing

-- | Apply a projection to an expression with a known type, returning
--   the type of the projected value.
--   The given type should either be a record type or a type eligible for
--   the principal argument of a projection-like function.
shouldBeProjectible :: (PureTCM m, MonadTCError m, MonadBlock m)
                    => Term -> Type -> ProjOrigin -> QName -> m Type
-- shouldBeProjectible t f = maybe failure return =<< projectionType t f
shouldBeProjectible v t o f = do
  t <- abortIfBlocked t
  projectTyped v t o f >>= \case
    Just (_ , _ , ft) -> return ft
    Nothing -> case t of
      El _ Dummy{} -> return __DUMMY_TYPE__
      _ -> typeError $ ShouldBeRecordType t
    -- TODO: more accurate error that makes sense also for proj.-like funs.

-- | The analogue of 'piApply'.  If @v@ is a value of record type @t@
--   with field @f@, then @projectTyped v t f@ returns the type of @f v@.
--   And also the record type (as first result).
--
--   Works also for projection-like definitions @f@.
--   In this case, the first result is not a record type.
--
--   Precondition: @t@ is reduced.
--
projectTyped
  :: PureTCM m
  => Term        -- ^ Head (record value).
  -> Type        -- ^ Its type.
  -> ProjOrigin
  -> QName       -- ^ Projection.
  -> m (Maybe (Dom Type, Term, Type))
projectTyped v t o f = caseMaybeM (getDefType f t) (return Nothing) $ \ tf -> do
  ifNotPiType tf (const $ return Nothing) {- else -} $ \ dom b -> do
  u <- applyDef o f (argFromDom dom $> v)
  return $ Just (dom, u, b `absApp` v)

-- | Typing of an elimination.

data ElimType
  = ArgT (Dom Type)           -- ^ Type of the argument.
  | ProjT
    { projTRec   :: Dom Type  -- ^ The type of the record which is eliminated.
    , projTField :: Type      -- ^ The type of the field.
    }

instance PrettyTCM ElimType where
  prettyTCM (ArgT a)    = prettyTCM a
  prettyTCM (ProjT a b) =
    "." <> parens (prettyTCM a <+> "->" <+> prettyTCM b)

-- | Given a head and its type, compute the types of the eliminations.

typeElims :: Type -> Term -> Elims -> TCM [ElimType]
typeElims a _ [] = return []
typeElims a self (e : es) = do
  case e of
    -- Andrea 02/08/2017: when going from patterns to elims we
    -- generate an Apply elim even for Path types, because we use VarP
    -- for both, so we have to allow for a Path type here.
    Apply v -> ifNotPiOrPathType a __IMPOSSIBLE__ {- else -} $ \ a b -> do
      (ArgT a :) <$> typeElims (absApp b $ unArg v) (self `applyE` [e]) es
    Proj o f -> do
      a <- reduce a
      (dom, self, a) <- fromMaybe __IMPOSSIBLE__ <$> projectTyped self a o f
      (ProjT dom a :) <$> typeElims a self es
    IApply{} -> __IMPOSSIBLE__

-- | Given a term with a given type and a list of eliminations, returning the
--   type of the term applied to the eliminations.
eliminateType :: (PureTCM m) => m Empty -> Term -> Type -> Elims -> m Type
eliminateType err = eliminateType' err . applyE

eliminateType' :: (PureTCM m) => m Empty -> (Elims -> Term) -> Type -> Elims -> m Type
eliminateType' err hd t [] = return t
eliminateType' err hd t (e : es) = case e of
  Apply v -> do
    t' <- piApplyM' err t v
    eliminateType' err (hd . (e:)) t' es
  Proj o f -> reduce t >>= getDefType f >>= \case
    Just a -> ifNotPiType a (\_ -> absurd <$> err) $ \_ c ->
      eliminateType' err (hd . (e:)) (c `absApp` (hd [])) es
    Nothing -> absurd <$> err
  IApply _ _ r -> do
    t' <- piApplyM' err t r
    eliminateType' err (hd . (e:)) t' es

-- | Check if a name refers to an eta expandable record.
--
-- The answer is no for a record type with an erased constructor
-- unless the current quantity is \"erased\".
{-# SPECIALIZE isEtaRecord :: QName -> TCM Bool #-}
{-# SPECIALIZE isEtaRecord :: QName -> ReduceM Bool #-}
isEtaRecord :: HasConstInfo m => QName -> m Bool
isEtaRecord r = do
  isRecord r >>= \case
    Just r | isEtaRecordDef r -> do
     constructorQ <- getQuantity <$> getConstInfo (conName (_recConHead r))
     currentQ     <- viewTC eQuantity
     return $ constructorQ `moreQuantity` currentQ
    _ -> return False

isEtaRecordDef :: RecordData -> Bool
isEtaRecordDef r = _recEtaEquality r == YesEta

{-# SPECIALIZE isEtaCon :: QName -> TCM Bool #-}
isEtaCon :: HasConstInfo m => QName -> m Bool
isEtaCon c = isJust <$> isEtaRecordConstructor c

-- | Going under one of these does not count as a decrease in size for the termination checker.
isEtaOrCoinductiveRecordConstructor :: HasConstInfo m => QName -> m Bool
isEtaOrCoinductiveRecordConstructor c =
  caseMaybeM (isRecordConstructor c) (return False) $ \ (_, def) ->
    pure (isEtaRecordDef def) `or2M`
      return (_recInduction def /= Just Inductive)
      -- If in doubt about coinductivity, then yes.

-- | Check if a name refers to a record which is not coinductive.  (Projections are then size-preserving)
isInductiveRecord :: HasConstInfo m => QName -> m Bool
isInductiveRecord r = maybe False ((Just CoInductive /=) . _recInduction) <$> isRecord r

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: (HasConstInfo m)
  => Type
  -> m (Maybe (QName, Args))
isEtaRecordType a = case unEl a of
  Def d es -> do
    let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    ifM (isEtaRecord d) (return $ Just (d, vs)) (return Nothing)
  _        -> return Nothing

-- | Check if a name refers to a record constructor.
--   If yes, return record definition.
--
isRecordConstructor :: HasConstInfo m => QName -> m (Maybe (QName, RecordData))
isRecordConstructor c = getConstInfo' c >>= \case
  Left (SigUnknown err)     -> __IMPOSSIBLE__
  Left SigCubicalNotErasure -> __IMPOSSIBLE__
  Left SigAbstract          -> return Nothing
  Right def                 -> case theDef $ def of
    Constructor{ conData = r } -> fmap (r,) <$> isRecord r
    _                          -> return Nothing

isEtaRecordConstructor :: HasConstInfo m => QName -> m (Maybe (QName, RecordData))
isEtaRecordConstructor c = isRecordConstructor c >>= \case
  Nothing -> return Nothing
  Just (d, def) -> if isEtaRecordDef def then return $ Just (d, def) else return Nothing

-- | Turn off eta for unguarded recursive records.
--   Projections do not preserve guardedness.
unguardedRecord :: QName -> PatternOrCopattern -> TCM ()
unguardedRecord q pat = modifyRecEta q \ eta -> setEtaEquality eta $ NoEta pat

-- | Turn on eta for non-recursive and inductive guarded recursive records,
--   unless user declared otherwise.
--   Projections do not preserve guardedness.
updateEtaForRecord :: QName -> TCM ()
updateEtaForRecord q = whenM etaEnabled $ do

  -- Do we need to switch on eta for record q?
  switchEta <- getConstInfo q <&> theDef <&> \case
    Record{ recInduction = ind, recEtaEquality' = eta }
      | Inferred NoEta{} <- eta, ind /= Just CoInductive -> True
      | otherwise -> False
    _ -> __IMPOSSIBLE__

  when switchEta $ modifyRecEta q $ const $ Inferred YesEta

-- | Turn on eta for inductive guarded recursive records.
--   Projections do not preserve guardedness.
recursiveRecord :: QName -> TCM ()
recursiveRecord = updateEtaForRecord

-- | Turn on eta for non-recursive record, unless user declared otherwise.
nonRecursiveRecord :: QName -> TCM ()
nonRecursiveRecord = updateEtaForRecord

-- | Check whether record type is marked as recursive.
--
--   Precondition: record type identifier exists in signature.
isRecursiveRecord :: QName -> TCM Bool
isRecursiveRecord q =
  getSignature <&> lookupDefinition q <&> fmap theDef <&> \case
    Just (RecordDefn r) -> recRecursive_ r
    _ -> __IMPOSSIBLE__

{- | @etaExpandBoundVar i = (Δ, σ, τ)@

Precondition: The current context is @Γ = Γ₁, x:R pars, Γ₂@ where
  @|Γ₂| = i@ and @R@ is a eta-expandable record type
  with constructor @c@ and fields @Γ'@.

Postcondition: @Δ = Γ₁, Γ', Γ₂[c Γ']@ and @Γ ⊢ σ : Δ@ and @Δ ⊢ τ : Γ@.
-}
etaExpandBoundVar :: Int -> TCM (Maybe (Telescope, Substitution, Substitution))
etaExpandBoundVar i = fmap (\ (delta, sigma, tau, _) -> (delta, sigma, tau)) <$> do
  expandRecordVar i =<< getContextTelescope

-- | @expandRecordVar i Γ = (Δ, σ, τ, Γ')@
--
--   Precondition: @Γ = Γ₁, x:R pars, Γ₂@ where
--     @|Γ₂| = i@ and @R@ is a eta-expandable record type
--     with constructor @c@ and fields @Γ'@.
--
--   Postcondition: @Δ = Γ₁, Γ', Γ₂[c Γ']@ and @Γ ⊢ σ : Δ@ and @Δ ⊢ τ : Γ@.

expandRecordVar :: PureTCM m => Int -> Telescope -> m (Maybe (Telescope, Substitution, Substitution, Telescope))
expandRecordVar i gamma0 = do
  -- Get the context with last variable added last in list.
  let gamma = telToList gamma0
  -- Convert the de Bruijn index i to a de Bruijn level
      l     = size gamma - 1 - i
  -- Extract type of @i@th de Bruijn index.
  -- Γ = Γ₁, x:a, Γ₂
  let (gamma1, dom@(Dom{domInfo = ai, unDom = (x, a)}) : gamma2) = splitAt l gamma -- TODO:: Defined but not used dom, ai
  -- This must be a eta-expandable record type.
  let failure = do
        reportSDoc "tc.meta.assign.proj" 25 $
          "failed to eta-expand variable " <+> pretty x <+>
          " since its type " <+> prettyTCM a <+>
          " is not a record type"
        return Nothing
  caseMaybeM (isRecordType a) failure $ \ (r, pars, def) -> case isEtaRecordDef def of
    False -> return Nothing
    True  -> Just <$> do
      -- Get the record fields @Γ₁ ⊢ tel@ (@tel = Γ'@).
      -- TODO: compose argInfo ai with tel.
      let tel = _recTel def `apply` pars
          m   = size tel
          fs  = map argFromDom $ _recFields def
      -- Construct the record pattern @Γ₁, Γ' ⊢ u := c ys@.
          ys  = zipWith (\ f i -> f $> var i) fs $ downFrom m
          u   = mkCon (_recConHead def) ConOSystem ys
      -- @Γ₁, Γ' ⊢ τ₀ : Γ₁, x:_@
          tau0 = consS u $ raiseS m
      -- @Γ₁, Γ', Γ₂ ⊢ τ₀ : Γ₁, x:_, Γ₂@
          tau  = liftS (size gamma2) tau0

      --  Fields are in order first-first.
          zs  = for fs $ fmap $ \ f -> Var 0 [Proj ProjSystem f]
      --  We need to reverse the field sequence to build the substitution.
      -- @Γ₁, x:_ ⊢ σ₀ : Γ₁, Γ'@
          sigma0 = reverse (map unArg zs) ++# raiseS 1
      -- @Γ₁, x:_, Γ₂ ⊢ σ₀ : Γ₁, Γ', Γ₂@
          sigma  = liftS (size gamma2) sigma0

      -- Construct @Δ@ as telescope.
      -- Note @Γ₁, x:_ ⊢ Γ₂@, thus, @Γ₁, Γ' ⊢ [τ₀]Γ₂@

          -- Use "f(x)" as variable name for the projection f(x).
          s     = prettyShow x
          tel'  = mapAbsNames (\ f -> stringToArgName $ argNameToString f ++ "(" ++ s ++ ")") tel
          delta = telFromList $ gamma1 ++ telToList tel' ++
                    telToList (applySubst tau0 $ telFromList gamma2)
                    -- Andreas, 2017-07-29, issue #2644
                    -- We cannot substitute directly into a ListTel like gamma2,
                    -- we have to convert it to a telescope first, otherwise we get garbage.

      return (delta, sigma, tau, tel)

-- | Precondition: variable list is ordered descendingly.  Can be empty.
expandRecordVarsRecursively :: [Int] -> Telescope -> TCM (Telescope, Substitution, Substitution)
expandRecordVarsRecursively [] gamma = return (gamma, idS, idS)
expandRecordVarsRecursively (i : is) gamma = do
  caseMaybeM (expandRecordVar i gamma) (expandRecordVarsRecursively is gamma)
  $ \ (gamma1, sigma1, tau1, tel) -> do
    -- Γ ⊢ σ₁ : Γ₁  and  Γ₁ ⊢ τ₁ : Γ
    let n = size tel
        newis = take n $ downFrom $ i + n
    (gamma2, sigma2, tau2) <- expandRecordVarsRecursively (newis ++ is) gamma1
    -- Γ₁ ⊢ σ₂ : Γ₂  and  Γ₂ ⊢ τ₂ : Γ₁
    return (gamma2, applySubst sigma1 sigma2, applySubst tau2 tau1)

-- | @curryAt v (Γ (y : R pars) -> B) n =
--     ( \ v -> λ Γ ys → v Γ (c ys)            {- curry   -}
--     , \ v -> λ Γ y → v Γ (p1 y) ... (pm y)  {- uncurry -}
--     , Γ (ys : As) → B[c ys / y]
--     )@
--
--   where @n = size Γ@.
curryAt :: Type -> Int -> TCM (Term -> Term, Term -> Term, Type)
curryAt t n = do
  -- first, strip the leading n domains (which remain unchanged)
  TelV gamma core <- telViewUpTo n t
  case unEl core of
    -- There should be at least one domain left
    Pi (dom@Dom{domInfo = ai, unDom = a}) b -> do
      -- Eta-expand @dom@ along @qs@ into a telescope @tel@, computing a substitution.
      -- For now, we only eta-expand once.
      -- This might trigger another call to @etaExpandProjectedVar@ later.
      -- A more efficient version does all the eta-expansions at once here.
      (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType a
      if | NoEta _ <- _recEtaEquality def -> __IMPOSSIBLE__
         | otherwise -> return ()
      -- TODO: compose argInfo ai with tel.
      let tel = _recTel def `apply` pars
          m   = size tel
          fs  = map argFromDom $ _recFields def
          ys  = zipWith (\ f i -> f $> var i) fs $ downFrom m
          u   = mkCon (killRange $ _recConHead def) ConOSystem ys
          b'  = raise m b `absApp` u
          t'  = gamma `telePi` (tel `telePi` b')
          gammai = map domInfo $ telToList gamma
          xs  = reverse $ zipWith (\ ai i -> Arg ai $ var i) gammai [m..]
          curry v = teleLam gamma $ teleLam tel $
                      raise (n + m) v `apply` (xs ++ [Arg ai u])
          zs  = for fs $ fmap $ \ f -> Var 0 [Proj ProjSystem f]
          atel = sgTel $ (,) (absName b) <$> dom
          uncurry v = teleLam gamma $ teleLam atel $
                        raise (n + 1) v `apply` (xs ++ zs)
      return (curry, uncurry, t')
    _ -> __IMPOSSIBLE__

{-| @etaExpand r pars u@ computes the eta expansion of record value @u@
    at record type @r pars@.

    The first argument @r@ should be the name of an eta-expandable record type.
    Given

      @record R : Set where field x : A; y : B; .z : C@

    and @r : R@,

      @etaExpand R [] r = (tel, [R.x r, R.y r, R.z r])@

    where @tel@ is the record telescope instantiated at the parameters @pars@.
-}
etaExpandRecord :: (HasConstInfo m, MonadDebug m, ReadTCState m)
  => QName       -- ^ Name of record type.
  -> Args        -- ^ Parameters applied to record type.
  -> Term        -- ^ Term to eta-expand.
  -> m (Telescope, Args)
     -- ^ Field types instantiated to parameters, field values.
etaExpandRecord = etaExpandRecord' False

-- | Eta expand a record regardless of whether it's an eta-record or not.
forceEtaExpandRecord :: (HasConstInfo m, MonadDebug m, ReadTCState m, MonadError TCErr m)
  => QName       -- ^ Name of record type.
  -> Args        -- ^ Parameters applied to record type.
  -> Term        -- ^ Term to eta-expand.
  -> m (Telescope, Args)
     -- ^ Field types instantiated to parameters, field values.
forceEtaExpandRecord = etaExpandRecord' True

-- | Eta-expand a value at the given record type (must match).
etaExpandRecord' :: (HasConstInfo m, MonadDebug m, ReadTCState m)
  => Bool        -- ^ Force expansion, overriding '_recEtaEquality'?
  -> QName       -- ^ Name of record type.
  -> Args        -- ^ Parameters applied to record type.
  -> Term        -- ^ Term to eta-expand.
  -> m (Telescope, Args)
     -- ^ Field types instantiated to parameters, field values.
etaExpandRecord' forceEta r pars u = do
  def <- fromMaybe __IMPOSSIBLE__ <$> isRecord r
  (tel, _, _, args) <- etaExpandRecord'_ forceEta r pars def u
  return (tel, args)

-- | Eta-expand a value at the given eta record type (must match).
etaExpandRecord_ :: HasConstInfo m
  => QName       -- ^ Name of record type.
  -> Args        -- ^ Parameters applied to record type.
  -> RecordData  -- ^ Definition of record type.
  -> Term        -- ^ Term to eta-expand.
  -> m (Telescope, ConHead, ConInfo, Args)
     -- ^ Field types instantiated to parameters, disassembled constructor term.
etaExpandRecord_ = etaExpandRecord'_ False

-- | Eta-expand a value at the given record type (must match).
etaExpandRecord'_ :: HasConstInfo m
  => Bool        -- ^ Force expansion, overriding '_recEtaEquality'?
  -> QName       -- ^ Name of record type.
  -> Args        -- ^ Parameters applied to record type.
  -> RecordData  -- ^ Definition of record type.
  -> Term        -- ^ Term to eta-expand.
  -> m (Telescope, ConHead, ConInfo, Args)
     -- ^ Field types instantiated to parameters, disassembled constructor term.
etaExpandRecord'_ forceEta r pars
    def@RecordData{ _recConHead = con, _recFields = xs, _recTel = tel }
    u = do
  let tel' = apply tel pars
  -- Make sure we do not expand non-eta records (unless forced to):
  unless (_recEtaEquality def == YesEta || forceEta) __IMPOSSIBLE__
  case u of

    -- Already expanded.
    Con con_ ci es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- Andreas, 2019-10-21, issue #4148
      -- @con == con_@ might fail, but their normal forms should be equal.
      whenNothingM (conName con `sameDef` conName con_) $ do
        reportSDoc "impossible" 10 $ vcat
          [ "etaExpandRecord_: the following two constructors should be identical"
          , nest 2 $ text $ "con  = " ++ prettyShow con
          , nest 2 $ text $ "con_ = " ++ prettyShow con_
          ]
        __IMPOSSIBLE__
      return (tel', con, ci, args)

    -- Not yet expanded.
    _ -> do
      -- Andreas, < 2016-01-18: Note: recFields are always the original projections,
      -- thus, we can use them in Proj directly.
      let xs' = for (map argFromDom xs) $ fmap $ \ x -> u `applyE` [Proj ProjSystem x]
      reportSDoc "tc.record.eta" 20 $ vcat
        [ "eta expanding" <+> prettyTCM u <+> ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ "tel' =" <+> prettyTCM tel'
          , "args =" <+> prettyTCM xs'
          ]
        ]
      return (tel', con, ConOSystem, xs')

etaExpandAtRecordType :: Type -> Term -> TCM (Telescope, Term)
etaExpandAtRecordType t u = do
  (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType t
  (tel, con, ci, args) <- etaExpandRecord_ r pars def u
  return (tel, mkCon con ci args)

-- | The fields should be eta contracted already.
--
--   We can eta contract if all fields @f = ...@ are irrelevant
--   or all fields @f@ are the projection @f v@ of the same value @v@,
--   but we need at least one relevant field to find the value @v@.
--
--   If all fields are erased, we cannot eta-contract.

--   Andreas, 2019-11-06, issue #4168: eta-contraction all-erased record
--   lead to compilation error.

--   TODO: this can be moved out of TCM.
--   Andreas, 2018-01-28: attempted just that, but Auto does not
--   put the conFields there (it does not run in TCM).
--   If we get rid of Auto, we can do this.  (Tests not involving Auto pass.)

{-# SPECIALIZE etaContractRecord :: QName -> ConHead -> ConInfo -> Args -> TCM Term #-}
{-# SPECIALIZE etaContractRecord :: QName -> ConHead -> ConInfo -> Args -> ReduceM Term #-}
etaContractRecord :: HasConstInfo m => QName -> ConHead -> ConInfo -> Args -> m Term
etaContractRecord r c ci args = if all (not . usableModality) args then fallBack else do
  RecordData{ _recFields = xs } <- fromMaybe __IMPOSSIBLE__ <$> isRecord r
  reportSDoc "tc.record.eta.contract" 20 $ vcat
    [ "eta contracting record"
    , nest 2 $ vcat
      [ "record type r  =" <+> prettyTCM r
      , "constructor c  =" <+> prettyTCM c
      , "field names xs =" <+> pretty    xs
      , "fields    args =" <+> prettyTCM args
      ]
    ]
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      case zipWithM check args xs of
        Just as -> case catMaybes as of
          (a:as) ->
            if all (a ==) as
              then return a
              else fallBack
          _ -> fallBack -- just irrelevant terms
        _ -> fallBack  -- a Nothing
  where
  fallBack = return (mkCon c ci args)
  check :: Arg Term -> Dom QName -> Maybe (Maybe Term)
  check a ax = do
  -- @a@ is the constructor argument, @ax@ the corr. record field name
    -- skip irrelevant record fields by returning DontCare
    case (getRelevance a, hasElims $ unArg a) of
      (Irrelevant{}, _)   -> Just Nothing
      -- if @a@ is the record field name applied to a single argument
      -- then it passes the check
      (_, Just (_, [])) -> Nothing  -- not a projection
      (_, Just (h, e0:es0))
        | (es, Proj _o f) <- initLast1 e0 es0
        , unDom ax == f -> Just $ Just $ h es
      _                 -> Nothing

{-# SPECIALIZE isSingletonRecord :: QName -> Args -> TCM Bool #-}
-- | Is the type a hereditarily singleton record type? May return a
-- blocking metavariable.
--
-- Precondition: The name should refer to a record type, and the
-- arguments should be the parameters to the type.
isSingletonRecord :: (PureTCM m, MonadBlock m)
  => QName   -- ^ Name of record type to check.
  -> Args    -- ^ Parameters given to the record type.
  -> m Bool
isSingletonRecord r ps = isJust <$> isSingletonRecord' False r ps mempty

isSingletonRecordModuloRelevance :: (PureTCM m, MonadBlock m)
  => QName   -- ^ Name of record type to check.
  -> Args    -- ^ Parameters given to the record type.
  -> m Bool
isSingletonRecordModuloRelevance r ps = isJust <$> isSingletonRecord' True r ps mempty

-- | Return the unique (closed) inhabitant if exists.
--   In case of counting irrelevance in, the returned inhabitant
--   contains dummy terms.
isSingletonRecord'
  :: forall m. (PureTCM m, MonadBlock m)
  => Bool            -- ^ Should disregard irrelevant fields?
  -> QName           -- ^ Name of record type to check.
  -> Args            -- ^ Parameters given to the record type.
  -> Set QName       -- ^ Non-terminating record types we already encountered.
                     --   These are considered as non-singletons,
                     --   otherwise we would construct an infinite inhabitant (in an infinite time...).
  -> m (Maybe Term)  -- ^ The unique inhabitant, if any.  May contain dummy terms in irrelevant positions.
isSingletonRecord' regardIrrelevance r ps rs = do
  reportSDoc "tc.meta.eta" 30 $ vcat
    [ "Is" <+> prettyTCM (Def r $ map Apply ps) <+> "a singleton record type?"
    , "  already visited:" <+> hsep (map prettyTCM $ Set.toList rs)
    ]
  -- Andreas, 2022-03-10, issue #5823
  -- We need to make sure we are not infinitely unfolding records, so we only expand each once,
  -- and keep track of the recursive ones we have already seen.
  if r `Set.member` rs then no else do
    caseMaybeM (isRecord r) no $ \ def -> do
      -- We might not know yet whether a record type is recursive because the positivity checker hasn't run yet.
      -- In this case, we pessimistically consider the record type to be recursive (@True@).
      let recursive = maybe True (not . null) $ _recMutual def
      -- Andreas, 2022-03-23, issue #5823
      -- We may pass through terminating record types as often as we want.
      -- If the termination checker has not run yet, we pessimistically consider the record type
      -- to be non-terminating.
      let nonTerminating = maybe True not $ _recTerminates def
      reportSDoc "tc.meta.eta" 30 $ vcat
        [ hsep [ prettyTCM r, "is recursive      :", prettyTCM recursive      ]
        , hsep [ prettyTCM r, "is non-terminating:", prettyTCM nonTerminating ]
        ]
      fmap (mkCon (_recConHead def) ConOSystem) <$> do
        check (applyWhen (recursive && nonTerminating) (Set.insert r) rs) $ _recTel def `apply` ps
  where
  -- Check that all entries of the constructor telescope are singletons.
  check :: Set QName -> Telescope -> m (Maybe [Arg Term])
  check rs tel = do
    reportSDoc "tc.meta.eta" 30 $
      "isSingletonRecord' checking telescope " <+> prettyTCM tel
    case tel of
      EmptyTel -> yes
      ExtendTel dom tel -> ifM (return regardIrrelevance `and2M` isIrrelevantOrPropM dom)
        {-then-}
          (underAbstraction dom tel $ fmap (fmap (Arg (domInfo dom) __DUMMY_TERM__ :)) . check rs)
        {-else-} $ do
          caseMaybeM (isSingletonType' regardIrrelevance (unDom dom) rs) no $ \ v -> do
            underAbstraction dom tel $ fmap (fmap (Arg (domInfo dom) v :)) . check rs
  no  = return Nothing
  yes = return $ Just []

-- | Check whether a type has a unique inhabitant and return it.
--   Can be blocked by a metavar.
isSingletonType :: (PureTCM m, MonadBlock m) => Type -> m (Maybe Term)
isSingletonType t = isSingletonType' False t mempty

-- | Check whether a type has a unique inhabitant (irrelevant parts ignored).
--   Can be blocked by a metavar.
isSingletonTypeModuloRelevance :: (PureTCM m, MonadBlock m) => Type -> m Bool
isSingletonTypeModuloRelevance t = isJust <$> isSingletonType' True t mempty

isSingletonType'
  :: forall m. (PureTCM m, MonadBlock m)
  => Bool            -- ^ Should disregard irrelevant fields?
  -> Type            -- ^ Type to check.
  -> Set QName       -- ^ Non-terminating record typess we already encountered.
                     --   These are considered as non-singletons,
                     --   otherwise we would construct an infinite inhabitant (in an infinite time...).
  -> m (Maybe Term)  -- ^ The unique inhabitant, if any.  May contain dummy terms in irrelevant positions.
isSingletonType' regardIrrelevance t rs = do
    TelV tel t <- telView t
    t <- abortIfBlocked t
    addContext tel $ do
      let
        -- Easy case: η for records.
        record :: m (Maybe Term)
        record = runMaybeT $ do
          (r, ps, def) <- MaybeT $ isRecordType t
          guard $ isEtaRecordDef def
          abstract tel <$> MaybeT (isSingletonRecord' regardIrrelevance r ps rs)

        -- Slightly harder case: η for Sub {level} tA phi elt.
        -- tA : Type level, phi : I, elt : Partial phi tA.
        subtype :: m (Maybe Term)
        subtype = runMaybeT $ do
          (level, tA, phi, elt) <- MaybeT $ isCubicalSubtype t
          subin <- MaybeT $ getBuiltinName' builtinSubIn
          itIsOne <- MaybeT $ getBuiltinName' builtinIsOne
          phiV <- intervalView phi
          case phiV of
            -- If phi = i1, then inS (elt 1=1) is the only inhabitant.
            IOne -> do
              let
                argH = Arg $ setHiding Hidden defaultArgInfo
                it = elt `apply` [defaultArg (Def itIsOne [])]
              pure (Def subin [] `apply` [argH level, argH tA, argH phi, defaultArg it])
            -- Otherwise we're blocked
            OTerm phi' -> patternViolation (unblockOnAnyMetaIn phi')
            -- This fails the MaybeT: we're not looking at a
            -- definitional singleton.
            _ -> fail ""

      (<|>) <$> record <*> subtype

{-# SPECIALIZE isEtaVar :: Term -> Type -> TCM (Maybe Int) #-}
-- | Checks whether the given term (of the given type) is beta-eta-equivalent
--   to a variable. Returns just the de Bruijn-index of the variable if it is,
--   or nothing otherwise.
isEtaVar :: forall m. PureTCM m => Term -> Type -> m (Maybe Int)
isEtaVar u a = runMaybeT $ isEtaVarG u a Nothing []
  where
    -- Checks whether the term u (of type a) is beta-eta-equivalent to
    -- `Var i es`, and returns i if it is. If the argument mi is `Just i'`,
    -- then i and i' are also required to be equal (else Nothing is returned).
    isEtaVarG :: Term -> Type -> Maybe Int -> [Elim' Int] -> MaybeT m Int
    isEtaVarG u a mi es = do
      (u, a) <- reduce (u, a)
      reportSDoc "tc.lhs" 80 $ "isEtaVarG" <+> nest 2 (vcat
        [ "u  = " <+> prettyTCM u
        , "a  = " <+> prettyTCM a
        , "mi = " <+> text (show mi)
        , "es = " <+> prettyList_ (map (prettyTCM . fmap var) es)
        ])
      case (u, unEl a) of
        (Var i' es', _) -> do
          guard $ mi == (i' <$ mi)
          b <- typeOfBV i'
          areEtaVarElims (var i') b es' es
          return i'
        (_, Def d pars) -> do
          guard =<< do isEtaRecord d
          fs <- map unDom . recFields . theDef <$> getConstInfo d
          is <- forM fs $ \f -> do
            let o = ProjSystem
            (_, _, fa) <- MaybeT $ projectTyped u a o f
            isEtaVarG (u `applyE` [Proj o f]) fa mi (es ++ [Proj o f])
          case (mi, is) of
            (Just i, _)     -> return i
            (Nothing, [])   -> mzero
            (Nothing, i:is) -> guard (all (== i) is) >> return i
        (_, Pi dom cod) -> addContext dom $ do
          let u'  = raise 1 u `apply` [argFromDom dom $> var 0]
              a'  = absBody cod
              mi' = fmap (+ 1) mi
              es' = (fmap . fmap) (+ 1) es ++ [Apply $ argFromDom dom $> 0]
          (-1 +) <$> isEtaVarG u' a' mi' es'
        _ -> mzero

    -- `areEtaVarElims u a es es'` checks whether the given elims es (as applied
    -- to the term u of type a) are beta-eta-equal to either projections or
    -- variables with de Bruijn indices given by es'.
    areEtaVarElims :: Term -> Type -> Elims -> [Elim' Int] -> MaybeT m ()
    areEtaVarElims u a []    []    = return ()
    areEtaVarElims u a []    (_:_) = mzero
    areEtaVarElims u a (_:_) []    = mzero
    areEtaVarElims u a (Proj o f : es) (Proj _ f' : es') = do
      guard $ f == f'
      a       <- reduce a
      (_, _, fa) <- MaybeT $ projectTyped u a o f
      areEtaVarElims (u `applyE` [Proj o f]) fa es es'
    -- These two cases can occur only when we're looking at two different
    -- variables (i.e. one of function type and the other of record type) so
    -- it's definitely not the variable we're looking for (or someone is playing
    -- Jedi mind tricks on us)
    areEtaVarElims u a (Proj{}  : _ ) (Apply _ : _  ) = mzero
    areEtaVarElims u a (Apply _ : _ ) (Proj{}  : _  ) = mzero
    areEtaVarElims u a (Proj{} : _ ) (IApply{} : _  ) = mzero
    areEtaVarElims u a (IApply{} : _ ) (Proj{} : _  ) = mzero
    areEtaVarElims u a (Apply  _ : _ ) (IApply{} : _  ) = mzero
    areEtaVarElims u a (IApply{} : _ ) (Apply  _ : _  ) = mzero
    areEtaVarElims u a (IApply{} : _) (IApply{} : _) = __IMPOSSIBLE__ -- TODO Andrea: not actually impossible, should be done like Apply
    areEtaVarElims u a (Apply v : es) (Apply i : es') = do
      ifNotPiType a (const mzero) $ \dom cod -> do
      _ <- isEtaVarG (unArg v) (unDom dom) (Just $ unArg i) []
      areEtaVarElims (u `apply` [fmap var i]) (cod `absApp` var (unArg i)) es es'


-- | Replace projection patterns by the original projections.
--
class NormaliseProjP a where
  normaliseProjP :: HasConstInfo m => a -> m a

instance NormaliseProjP Clause where
  normaliseProjP cl = do
    ps <- normaliseProjP $ namedClausePats cl
    return $ cl { namedClausePats = ps }

instance NormaliseProjP a => NormaliseProjP (x, a) where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP a => NormaliseProjP [a] where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP a => NormaliseProjP (Arg a) where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP a => NormaliseProjP (Named_ a) where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP (Pattern' x) where
  normaliseProjP p@VarP{}        = return p
  normaliseProjP p@DotP{}        = return p
  normaliseProjP (ConP c cpi ps) = ConP c cpi <$> normaliseProjP ps
  normaliseProjP (DefP o q ps) = DefP o q <$> normaliseProjP ps
  normaliseProjP p@LitP{}        = return p
  normaliseProjP (ProjP o d0)    = ProjP o <$> getOriginalProjection d0
  normaliseProjP p@IApplyP{}     = return p
