{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Records where

-- import Control.Applicative
import Control.Monad

import Data.Function
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable (traverse)

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Concrete (FieldAssignment'(..), nameFieldA)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal as I
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad ()
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.ProjectionLike (eligibleForProjectionLike)

import Agda.Utils.Either
import Agda.Utils.Functor (for, ($>))
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Order the fields of a record construction.
--   Use the second argument for missing fields.
orderFields :: QName -> a -> [C.Name] -> [(C.Name, a)] -> TCM [a]
orderFields r def xs fs = do
  unlessNull (ys \\ nub ys) $ typeError . DuplicateFields . nub
  unlessNull (ys \\ xs)     $ typeError . TooManyFields r
  -- shouldBeNull (xs \\ ys)     $ TooFewFields r
  return $ order xs fs
  where
    ys = map fst fs

    -- invariant: the first list contains at least the fields of the second list
    order [] [] = []
    order [] _  = __IMPOSSIBLE__
    order (x : xs) ys = case lookup x (assocHoles ys) of
      Just (e, ys') -> e : order xs ys'
      Nothing       -> def : order xs ys

    assocHoles xs = [ (x, (v, xs')) | ((x, v), xs') <- holes xs ]

-- | A record field assignment @record{xs = es}@ might not mention all
--   visible fields.  @insertMissingFields@ inserts placeholders for
--   the missing visible fields and returns the values in order
--   of the fields in the record declaration.
insertMissingFields
  :: QName                -- ^ Name of record type (for error reporting).
  -> (C.Name -> a)        -- ^ Function to generate a placeholder for missing visible field.
  -> [FieldAssignment' a] -- ^ Given fields.
  -> [Arg C.Name]         -- ^ All record field names with 'ArgInfo'.
  -> TCM [NamedArg a]     -- ^ Given fields enriched by placeholders for missing explicit fields.
insertMissingFields r placeholder fs axs = do
  -- Compute the list of given fields, decorated with the ArgInfo from the record def.
  let arg x e =
        case [ a | a <- axs, unArg a == x ] of
          [a] -> nameIfHidden a e <$ a
          _   -> defaultNamedArg e -- we only end up here if the field names are bad
      givenFields = [ (x, Just $ arg x e) | FieldAssignment x e <- fs ]
  -- Compute a list of p[aceholders for the missing visible fields.
  let missingExplicits =
       [ (x, Just $ setOrigin Inserted $ nameIfHidden a . placeholder <$> a)
       | a <- filter visible axs
       , let x = unArg a
       , x `notElem` map (view nameFieldA) fs
       ]
  -- In es omitted explicit fields are replaced by placeholders
  -- (from missingExplicits). Omitted implicit or instance fields
  -- are still left out and inserted later by checkArguments_.
  catMaybes <$> do
    -- Default value @Nothing@ will only be used for missing hidden fields.
    -- These can be ignored as they will be inserted by @checkArguments_@.
    orderFields r Nothing (map unArg axs) $ givenFields ++ missingExplicits
  where
    -- Andreas, 2017-04-13, issue #2494
    -- We need to put the field names as argument names for hidden arguments.
    -- Otherwise, insertImplicit does not do the right thing.
    nameIfHidden :: Arg C.Name -> c -> Named_ c
    nameIfHidden ax
      | visible ax = unnamed
      | otherwise  = named (Ranged (getRange ax) $ prettyShow $ unArg ax)

-- | The name of the module corresponding to a record.
recordModule :: QName -> ModuleName
recordModule = mnameFromList . qnameToList

-- | Get the definition for a record. Throws an exception if the name
--   does not refer to a record or the record is abstract.
getRecordDef :: QName -> TCM Defn
getRecordDef r = maybe err return =<< isRecord r
  where err = typeError $ ShouldBeRecordType (El Prop $ Def r [])

-- | Get the record name belonging to a field name.
getRecordOfField :: QName -> TCM (Maybe QName)
getRecordOfField d = caseMaybeM (isProjection d) (return Nothing) $
  \ Projection{ projProper = proper, projFromType = r} ->
    return $ unArg r <$ proper -- if proper then Just (unArg r) else Nothing

-- | Get the field names of a record.
getRecordFieldNames :: QName -> TCM [Arg C.Name]
getRecordFieldNames r = recordFieldNames <$> getRecordDef r

recordFieldNames :: Defn -> [Arg C.Name]
recordFieldNames = map (fmap (nameConcrete . qnameName)) . recFields

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs  <- HMap.elems <$> use (stSignature . sigDefinitions)
  idefs <- HMap.elems <$> use (stImports   . sigDefinitions)
  return $ cands defs ++ cands idefs
  where
    cands defs = [ defName d | d <- defs, possible d ]
    possible def =
      -- Check whether the given fields are contained
      -- in the fields of record @def@ (if it is a record).
      case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given $
          Set.fromList $ map (nameConcrete . qnameName . unArg) fs
        _ -> False
    given = Set.fromList fields

-- | Get the field types of a record.
getRecordFieldTypes :: QName -> TCM Telescope
getRecordFieldTypes r = recTel <$> getRecordDef r

-- | Get the field names belonging to a record type.
getRecordTypeFields :: Type -> TCM [Arg QName]
getRecordTypeFields t =
  case ignoreSharing $ unEl t of
    Def r _ -> do
      rDef <- theDef <$> getConstInfo r
      case rDef of
        Record { recFields = fields } -> return fields
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

-- | Returns the given record type's constructor name (with an empty
-- range).
getRecordConstructor :: QName -> TCM ConHead
getRecordConstructor r = killRange <$> recConHead <$> getRecordDef r

-- | Check if a name refers to a record.
--   If yes, return record definition.
{-# SPECIALIZE isRecord :: QName -> TCM (Maybe Defn) #-}
{-# SPECIALIZE isRecord :: QName -> ReduceM (Maybe Defn) #-}
isRecord :: HasConstInfo m => QName -> m (Maybe Defn)
isRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{} -> Just def
    _        -> Nothing

-- | Reduce a type and check whether it is a record type.
--   Succeeds only if type is not blocked by a meta var.
--   If yes, return its name, parameters, and definition.
isRecordType :: Type -> TCM (Maybe (QName, Args, Defn))
isRecordType t = either (const Nothing) Just <$> tryRecordType t

-- | Reduce a type and check whether it is a record type.
--   Succeeds only if type is not blocked by a meta var.
--   If yes, return its name, parameters, and definition.
--   If no, return the reduced type (unless it is blocked).
tryRecordType :: Type -> TCM (Either (Maybe Type) (QName, Args, Defn))
tryRecordType t = ifBlockedType t (\ _ _ -> return $ Left Nothing) $ \ t -> do
  let no = return $ Left $ Just t
  case ignoreSharing $ unEl t of
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
getDefType :: QName -> Type -> TCM (Maybe Type)
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
    [ text "definition f = " <> prettyTCM f <+> text ("raw: " ++ show f)
    , text "has type   a = " <> prettyTCM a
    , text "principal  t = " <> prettyTCM t
    ]
  caseMaybe mp fallback $
    \ (Projection{ projIndex = n }) -> if n <= 0 then fallback else do
      -- otherwise, we have to instantiate @a@ to the "parameters" of @f@
      let npars | n == 0    = __IMPOSSIBLE__
                | otherwise = n - 1
      reportSLn "tc.deftype" 20 $ "projIndex    = " ++ show n
      -- we get the parameters from type @t@
      case ignoreSharing $ unEl t of
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
              [ text $ "head d     = " ++ show d
              , text "parameters =" <+> sep (map prettyTCM pars)
              ]
            reportSLn "tc.deftype" 60 $ "parameters = " ++ show pars
            if length pars < npars then failure "does not supply enough parameters"
            else Just <$> a `piApplyM` pars
        _ -> failNotDef
  where
    failNotElig = failure "is not eligible for projection-likeness"
    failNotDef  = failure "is not a Def."
    failure reason = do
      reportSDoc "tc.deftype" 25 $ sep
        [ text "Def. " <+> prettyTCM f <+> text " is projection(like)"
        , text "but the type "
        , prettyTCM t
        , text $ "of its argument " ++ reason
        ]
      return Nothing

-- | The analogue of 'piApply'.  If @v@ is a value of record type @t@
--   with field @f@, then @projectTyped v t f@ returns the type of @f v@.
--   And also the record type (as first result).
--
--   Works also for projection-like definitions @f@.
--   In this case, the first result is not a record type.
--
--   Precondition: @t@ is reduced.
projectTyped :: Term -> Type -> ProjOrigin -> QName -> TCM (Maybe (Dom Type, Term, Type))
projectTyped v t o f = caseMaybeM (getDefType f t) (return Nothing) $ \ tf -> do
  ifNotPiType tf (const $ return Nothing) {- else -} $ \ dom b -> do
  u <- applyDef o f (argFromDom dom $> v)
  return $ Just (dom, u, b `absApp` v)

-- | Check if a name refers to an eta expandable record.
{-# SPECIALIZE isEtaRecord :: QName -> TCM Bool #-}
{-# SPECIALIZE isEtaRecord :: QName -> ReduceM Bool #-}
isEtaRecord :: HasConstInfo m => QName -> m Bool
isEtaRecord r = maybe False recEtaEquality <$> isRecord r

isEtaCon :: HasConstInfo m => QName -> m Bool
isEtaCon c = do
  cdef <- theDef <$> getConstInfo c
  case cdef of
    Constructor {conData = r} -> isEtaRecord r
    _ -> return False

-- | Check if a name refers to a record which is not coinductive.  (Projections are then size-preserving)
isInductiveRecord :: QName -> TCM Bool
isInductiveRecord r = maybe False (\ d -> recInduction d /= Just CoInductive || not (recRecursive d)) <$> isRecord r

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: Type -> TCM (Maybe (QName, Args))
isEtaRecordType a = case ignoreSharing $ unEl a of
  Def d es -> do
    let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    ifM (isEtaRecord d) (return $ Just (d, vs)) (return Nothing)
  _        -> return Nothing

-- | Check if a name refers to a record constructor.
--   If yes, return record definition.
isRecordConstructor :: HasConstInfo m => QName -> m (Maybe (QName, Defn))
isRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> fmap (r,) <$> isRecord r
    _                          -> return Nothing

-- | Check if a constructor name is the internally generated record constructor.
isGeneratedRecordConstructor :: QName -> TCM Bool
isGeneratedRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> do
      def <- theDef <$> getConstInfo r
      case def of
        Record{ recNamedCon = False } -> return True
        _                             -> return False
    _ -> return False

-- | Turn off eta for unguarded recursive records.
--   Projections do not preserve guardedness.
unguardedRecord :: QName -> TCM ()
unguardedRecord q = modifySignature $ updateDefinition q $ updateTheDef $ \case
  r@Record{} -> r { recEtaEquality' = setEtaEquality (recEtaEquality' r) False }
  _ -> __IMPOSSIBLE__

-- | Turn on eta for inductive guarded recursive records.
--   Projections do not preserve guardedness.
recursiveRecord :: QName -> TCM ()
recursiveRecord q = do
  ok <- etaEnabled
  modifySignature $ updateDefinition q $ updateTheDef $ \case
    r@Record{ recInduction = ind, recEtaEquality' = eta } ->
      r { recEtaEquality' = eta' }
      where
      eta' | ok, eta == Inferred False, ind /= Just CoInductive = Inferred True
           | otherwise = eta
    _ -> __IMPOSSIBLE__

-- | Turn on eta for non-recursive record, unless user declared otherwise.
nonRecursiveRecord :: QName -> TCM ()
nonRecursiveRecord q = whenM etaEnabled $ do
  -- Do nothing if eta is disabled by option.
  modifySignature $ updateDefinition q $ updateTheDef $ \case
    r@Record{ recInduction = ind, recEtaEquality' = Inferred False }
      | ind /= Just CoInductive ->
      r { recEtaEquality' = Inferred True }
    r@Record{} -> r
    _          -> __IMPOSSIBLE__


-- | Check whether record type is marked as recursive.
--
--   Precondition: record type identifier exists in signature.
isRecursiveRecord :: QName -> TCM Bool
isRecursiveRecord q = recRecursive . theDef . fromMaybe __IMPOSSIBLE__ . lookupDefinition q <$> getSignature

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

expandRecordVar :: Int -> Telescope -> TCM (Maybe (Telescope, Substitution, Substitution, Telescope))
expandRecordVar i gamma0 = do
  -- Get the context with last variable added last in list.
  let gamma = telToList gamma0
  -- Convert the de Bruijn index i to a de Bruijn level
      l     = size gamma - 1 - i
  -- Extract type of @i@th de Bruijn index.
  -- Γ = Γ₁, x:a, Γ₂
  let (gamma1, dom@(Dom ai (x, a)) : gamma2) = splitAt l gamma
  -- This must be a eta-expandable record type.
  let failure = do
        reportSDoc "tc.meta.assign.proj" 25 $
          text "failed to eta-expand variable " <+> pretty x <+>
          text " since its type " <+> prettyTCM a <+>
          text " is not a record type"
        return Nothing
  caseMaybeM (isRecordType a) failure $ \ (r, pars, def) -> do
    if not (recEtaEquality def) then return Nothing else Just <$> do
      -- Get the record fields @Γ₁ ⊢ tel@ (@tel = Γ'@).
      -- TODO: compose argInfo ai with tel.
      let tel = recTel def `apply` pars
          m   = size tel
          fs  = recFields def
      -- Construct the record pattern @Γ₁, Γ' ⊢ u := c ys@.
          ys  = zipWith (\ f i -> f $> var i) fs $ downFrom m
          u   = Con (recConHead def) ConOSystem ys
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
          delta = telFromList $ gamma1 ++ telToList tel' ++ applySubst tau0 gamma2

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
  case ignoreSharing $ unEl core of
    -- There should be at least one domain left
    Pi (Dom ai a) b -> do
      -- Eta-expand @dom@ along @qs@ into a telescope @tel@, computing a substitution.
      -- For now, we only eta-expand once.
      -- This might trigger another call to @etaExpandProjectedVar@ later.
      -- A more efficient version does all the eta-expansions at once here.
      (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType a
      unless (recEtaEquality def) __IMPOSSIBLE__
      -- TODO: compose argInfo ai with tel.
      let tel = recTel def `apply` pars
          m   = size tel
          fs  = recFields def
          ys  = zipWith (\ f i -> f $> var i) fs $ downFrom m
          u   = Con (recConHead def) ConOSystem ys
          b'  = raise m b `absApp` u
          t'  = gamma `telePi` (tel `telePi` b')
          gammai = map domInfo $ telToList gamma
          xs  = reverse $ zipWith (\ ai i -> Arg ai $ var i) gammai [m..]
          curry v = teleLam gamma $ teleLam tel $
                      raise (n+m) v `apply` (xs ++ [Arg ai u])
          zs  = for fs $ fmap $ \ f -> Var 0 [Proj ProjSystem f]
          atel = sgTel $ Dom ai (absName b, a)
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
etaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord = etaExpandRecord' False

-- | Eta expand a record regardless of whether it's an eta-record or not.
forceEtaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
forceEtaExpandRecord = etaExpandRecord' True

etaExpandRecord' :: Bool -> QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord' forceEta r pars u = do
  def <- getRecordDef r
  (tel, _, _, args) <- etaExpandRecord'_ forceEta r pars def u
  return (tel, args)

etaExpandRecord_ :: QName -> Args -> Defn -> Term -> TCM (Telescope, ConHead, ConInfo, Args)
etaExpandRecord_ = etaExpandRecord'_ False

etaExpandRecord'_ :: Bool -> QName -> Args -> Defn -> Term -> TCM (Telescope, ConHead, ConInfo, Args)
etaExpandRecord'_ forceEta r pars def u = do
  let Record{ recConHead     = con
            , recFields      = xs
            , recTel         = tel
            } = def
      eta = recEtaEquality def
      tel' = apply tel pars
  unless (eta || forceEta) __IMPOSSIBLE__ -- make sure we do not expand non-eta records (unless forced to)
  case ignoreSharing u of

    -- Already expanded.
    Con con_ ci args -> do
      when (con /= con_) $ do
        reportSDoc "impossible" 10 $ vcat
          [ text "etaExpandRecord_: the following two constructors should be identical"
          , nest 2 $ text $ "con  = " ++ show con
          , nest 2 $ text $ "con_ = " ++ show con_
          ]
        __IMPOSSIBLE__
      return (tel', con, ci, args)

    -- Not yet expanded.
    _ -> do
      -- Andreas, < 2016-01-18: Note: recFields are always the original projections,
      -- thus, we can use them in Proj directly.
      let xs' = for xs $ fmap $ \ x -> u `applyE` [Proj ProjSystem x]
      reportSDoc "tc.record.eta" 20 $ vcat
        [ text "eta expanding" <+> prettyTCM u <+> text ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ text "tel' =" <+> prettyTCM tel'
          , text "args =" <+> prettyTCM xs'
          ]
        ]
      return (tel', con, ConOSystem, xs')

etaExpandAtRecordType :: Type -> Term -> TCM (Telescope, Term)
etaExpandAtRecordType t u = do
  (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType t
  (tel, con, ci, args) <- etaExpandRecord_ r pars def u
  return (tel, Con con ci args)

-- | The fields should be eta contracted already.
--
--   We can eta contract if all fields @f = ...@ are irrelevant
--   or all fields @f@ are the projection @f v@ of the same value @v@,
--   but we need at least one relevant field to find the value @v@.
--
--   TODO: this can be moved out of TCM (but only if ConHead
--   stores also the Arg-decoration of the record fields.
{-# SPECIALIZE etaContractRecord :: QName -> ConHead -> ConInfo -> Args -> TCM Term #-}
{-# SPECIALIZE etaContractRecord :: QName -> ConHead -> ConInfo -> Args -> ReduceM Term #-}
etaContractRecord :: HasConstInfo m => QName -> ConHead -> ConInfo -> Args -> m Term
etaContractRecord r c ci args = do
  Just Record{ recFields = xs } <- isRecord r
  let check :: Arg Term -> Arg QName -> Maybe (Maybe Term)
      check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (getRelevance a, hasElims $ unArg a) of
          (Irrelevant, _)   -> Just Nothing
          -- if @a@ is the record field name applied to a single argument
          -- then it passes the check
          (_, Just (_, [])) -> Nothing  -- not a projection
          (_, Just (h, es)) | Proj _o f <- last es, unArg ax == f
                            -> Just $ Just $ h $ init es
          _                 -> Nothing
      fallBack = return (Con c ci args)
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      case zipWithM check args xs of
        Just as -> case [ a | Just a <- as ] of
          (a:as) ->
            if all (a ==) as
              then return a
              else fallBack
          _ -> fallBack -- just irrelevant terms
        _ -> fallBack  -- a Nothing

-- | Is the type a hereditarily singleton record type? May return a
-- blocking metavariable.
--
-- Precondition: The name should refer to a record type, and the
-- arguments should be the parameters to the type.
isSingletonRecord :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecord r ps = mapRight isJust <$> isSingletonRecord' False r ps

isSingletonRecordModuloRelevance :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecordModuloRelevance r ps = mapRight isJust <$> isSingletonRecord' True r ps

-- | Return the unique (closed) inhabitant if exists.
--   In case of counting irrelevance in, the returned inhabitant
--   contains garbage.
isSingletonRecord' :: Bool -> QName -> Args -> TCM (Either MetaId (Maybe Term))
isSingletonRecord' regardIrrelevance r ps = do
  reportSLn "tc.meta.eta" 30 $ "Is " ++ show r ++ " a singleton record type?"
  def <- getRecordDef r
  emap (Con (recConHead def) ConOSystem) <$> check (recTel def `apply` ps)
  where
  check :: Telescope -> TCM (Either MetaId (Maybe [Arg Term]))
  check tel = do
    reportSDoc "tc.meta.eta" 30 $
      text "isSingletonRecord' checking telescope " <+> prettyTCM tel
    case tel of
      EmptyTel -> return $ Right $ Just []
      ExtendTel dom tel
        | isIrrelevant dom && regardIrrelevance -> do
          underAbstraction dom tel $ \ tel ->
            emap (Arg (domInfo dom) garbage :) <$> check tel
        | otherwise -> do
          isSing <- isSingletonType' regardIrrelevance $ unDom dom
          case isSing of
            Left mid       -> return $ Left mid
            Right Nothing  -> return $ Right Nothing
            Right (Just v) -> underAbstraction dom tel $ \ tel ->
              emap (Arg (domInfo dom) v :) <$> check tel
  garbage :: Term
  garbage = Sort Prop

-- | Check whether a type has a unique inhabitant and return it.
--   Can be blocked by a metavar.
isSingletonType :: Type -> TCM (Either MetaId (Maybe Term))
isSingletonType = isSingletonType' False

-- | Check whether a type has a unique inhabitant (irrelevant parts ignored).
--   Can be blocked by a metavar.
isSingletonTypeModuloRelevance :: (MonadTCM tcm) => Type -> tcm (Either MetaId Bool)
isSingletonTypeModuloRelevance t = liftTCM $ do
  mapRight isJust <$> isSingletonType' True t

isSingletonType' :: Bool -> Type -> TCM (Either MetaId (Maybe Term))
isSingletonType' regardIrrelevance t = do
    TelV tel t <- telView t
    ifBlockedType t (\ m _ -> return $ Left m) $ \ t -> do
      res <- isRecordType t
      case res of
        Just (r, ps, def) | recEtaEquality def -> do
          emap (abstract tel) <$> isSingletonRecord' regardIrrelevance r ps
        _ -> return $ Right Nothing

-- | Auxiliary function.
emap :: (a -> b) -> Either c (Maybe a) -> Either c (Maybe b)
emap = mapRight . fmap

class NormaliseProjP a where
  normaliseProjP :: HasConstInfo m => a -> m a

instance NormaliseProjP Clause where
  normaliseProjP cl = do
    ps <- normaliseProjP $ namedClausePats cl
    return $ cl { namedClausePats = ps }

instance NormaliseProjP a => NormaliseProjP [a] where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP a => NormaliseProjP (Arg a) where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP a => NormaliseProjP (Named_ a) where
  normaliseProjP = traverse normaliseProjP

instance NormaliseProjP (Pattern' x) where
  normaliseProjP p@VarP{}        = return p
  normaliseProjP p@DotP{}        = return p
  normaliseProjP p@AbsurdP{}     = return p
  normaliseProjP (ConP c cpi ps) = ConP c cpi <$> normaliseProjP ps
  normaliseProjP p@LitP{}        = return p
  normaliseProjP (ProjP o d0)    = ProjP o <$> getOriginalProjection d0
