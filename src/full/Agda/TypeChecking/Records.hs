{-# LANGUAGE CPP, TupleSections, PatternGuards #-}

module Agda.TypeChecking.Records where

-- import Control.Applicative
import Control.Monad

import Data.Function
import Data.List
import Data.Maybe
import qualified Data.Set as Set

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Monad
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Order the fields of a record construction.
--   Use the second argument for missing fields.
orderFields :: QName -> a -> [C.Name] -> [(C.Name, a)] -> TCM [a]
orderFields r def xs fs = do
  shouldBeNull (ys \\ nub ys) $ DuplicateFields . nub
  shouldBeNull (ys \\ xs)     $ TooManyFields r
  -- shouldBeNull (xs \\ ys)     $ TooFewFields r
  return $ order xs fs
  where
    ys = map fst fs

    shouldBeNull [] err = return ()
    shouldBeNull xs err = typeError $ err xs

    -- invariant: the first list contains at least the fields of the second list
    order [] [] = []
    order [] _  = __IMPOSSIBLE__
    order (x : xs) ys = case lookup x (assocHoles ys) of
      Just (e, ys') -> e : order xs ys'
      Nothing       -> def : order xs ys

    assocHoles xs = [ (x, (v, xs')) | ((x, v), xs') <- holes xs ]

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
getRecordOfField d = maybe Nothing fromP <$> isProjection d
  where fromP Projection{ projProper = mp, projFromType = r} = mp $> r

-- | Get the field names of a record.
getRecordFieldNames :: QName -> TCM [I.Arg C.Name]
getRecordFieldNames r = recordFieldNames <$> getRecordDef r

recordFieldNames :: Defn -> [I.Arg C.Name]
recordFieldNames = map (fmap (nameConcrete . qnameName)) . recFields

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs <- (HMap.union `on` sigDefinitions) <$> getSignature <*> getImportedSignature
  let possible def = case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given inrecord
          where inrecord = Set.fromList $ map (nameConcrete . qnameName . unArg) fs
        _ -> False
  return [ defName d | d <- HMap.elems defs, possible d ]
  where
    given = Set.fromList fields

-- | Get the field types of a record.
getRecordFieldTypes :: QName -> TCM Telescope
getRecordFieldTypes r = recTel <$> getRecordDef r

-- | Get the field names belonging to a record type.
getRecordTypeFields :: Type -> TCM [I.Arg QName]
getRecordTypeFields t =
  case ignoreSharing $ unEl t of
    Def r _ -> do
      rDef <- theDef <$> getConstInfo r
      case rDef of
        Record { recFields = fields } -> return fields
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__


-- | Get the type of the record constructor.
getRecordConstructorType :: QName -> TCM Type
getRecordConstructorType r = recConType <$> getRecordDef r

-- | Returns the given record type's constructor name (with an empty
-- range).
getRecordConstructor :: QName -> TCM ConHead
getRecordConstructor r = killRange <$> recConHead <$> getRecordDef r

-- | Check if a name refers to a record.
--   If yes, return record definition.
isRecord :: QName -> TCM (Maybe Defn)
isRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{} -> Just def
    _        -> Nothing

-- | Reduce a type and check whether it is a record type.
--   Succeeds only if type is not blocked by a meta var.
--   If yes, return its name, parameters, and definition.
isRecordType :: Type -> TCM (Maybe (QName, Args, Defn))
isRecordType t = ifBlockedType t (\ _ _ -> return Nothing) $ \ t -> do
  case ignoreSharing $ unEl t of
    Def r es -> do
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      fmap (r,vs,) <$> isRecord r
    _        -> return Nothing

-- | The analogue of 'piApply'.  If @v@ is a value of record type @T@
--   with field @f@, then @projectType T f@ returns the type of @f v@.
projectType :: Type -> QName -> TCM (Maybe Type)
projectType t f = do
  res <- isRecordType t
  case res of
    Nothing -> return Nothing
    Just (_r, ps, _rdef) -> do
      def <- getConstInfo f
      if (isProperProjection $ theDef def)
        then return $ Just $ defType def `apply` ps
        else return Nothing

{- DEPRECATED, use Signature.getDefType instead!

-- | @projectionType t f@ returns the type of projection or
--   projection-like function @t@ applied to the parameters,
--   which are read of @t@.
--   It fails if @t@ is not a @Def@ applied to the parameters.
projectionType :: Type -> QName -> TCM (Maybe Type)
projectionType t f = do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Def _ es -> do
      flip (maybe $ return Nothing) (allApplyElims es) $ \ pars -> do
        ft <- defType <$> getConstInfo f  -- type of projection(like) function
        return $ Just $ ft `piApply` pars
    _ -> return Nothing
-}

-- | Check if a name refers to an eta expandable record.
isEtaRecord :: QName -> TCM Bool
isEtaRecord r = maybe False recEtaEquality <$> isRecord r

-- | Check if a name refers to a record which is not coinductive.  (Projections are then size-preserving)
isInductiveRecord :: QName -> TCM Bool
isInductiveRecord r = maybe False (\ d -> recInduction d == Inductive || not (recRecursive d)) <$> isRecord r

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: Type -> TCM (Maybe (QName, Args))
isEtaRecordType a = case ignoreSharing $ unEl a of
  Def d es -> do
    let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    ifM (isEtaRecord d) (return $ Just (d, vs)) (return Nothing)
  _        -> return Nothing

-- | Check if a name refers to a record constructor.
--   If yes, return record definition.
isRecordConstructor :: QName -> TCM (Maybe (QName, Defn))
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

-- | Mark record type as unguarded.
--   No eta-expansion.  Projections do not preserve guardedness.
unguardedRecord :: QName -> TCM ()
unguardedRecord q = modifySignature $ updateDefinition q $ updateTheDef $ updateRecord
  where updateRecord r@Record{} = r { recEtaEquality = False, recRecursive = True }
        updateRecord _          = __IMPOSSIBLE__

-- | Mark record type as recursive.
--   Projections do not preserve guardedness.
recursiveRecord :: QName -> TCM ()
recursiveRecord q = modifySignature $ updateDefinition q $ updateTheDef $ updateRecord
  where updateRecord r@Record{} = r { recRecursive = True }
        updateRecord _          = __IMPOSSIBLE__

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
          u   = Con (recConHead def) ys
          b'  = raise m b `absApp` u
          t'  = gamma `telePi` (tel `telePi` b')
          gammai = map domInfo $ telToList gamma
          xs  = reverse $ zipWith (\ ai i -> Arg ai $ var i) gammai [m..]
          curry v = teleLam gamma $ teleLam tel $
                      raise (n+m) v `apply` (xs ++ [Arg ai u])
          zs  = for fs $ fmap $ \ f -> Var 0 [Proj f]
          atel = sgTel $ Dom ai (absName b, a)
          uncurry v = teleLam gamma $ teleLam atel $
                        raise (n + 1) v `apply` (xs ++ zs)
      return (curry, uncurry, t')
    _ -> __IMPOSSIBLE__

{-| @etaExpand r pars u@ computes the eta expansion of record value @u@
    at record type @r pars@.

    The first argument @r@ should be the name of a record type. Given

      @record R : Set where field x : A; y : B; .z : C@

    and @r : R@,

      @etaExpand R [] r = (tel, [R.x r, R.y r, R.z r])@

    where @tel@ is the record telescope instantiated at the parameters @pars@.
-}
etaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord r pars u = do
  def <- getRecordDef r
  (tel, _, args) <- etaExpandRecord_ r pars def u
  return (tel, args)

etaExpandRecord_ :: QName -> Args -> Defn -> Term -> TCM (Telescope, ConHead, Args)
etaExpandRecord_ r pars def u = do
  let Record{ recConHead     = con
            , recFields      = xs
            , recTel         = tel
            , recEtaEquality = eta
            } = def
      tel' = apply tel pars
  unless eta __IMPOSSIBLE__ -- make sure we do not expand non-eta records
  case ignoreSharing u of
    -- Already expanded.
    Con con_ args -> do
      when (con /= con_) __IMPOSSIBLE__
      return (tel', con, args)
    -- Not yet expanded.
    _             -> do
      let xs' = for xs $ fmap $ \ x -> u `applyE` [Proj x]
{- recFields are always the original projections
      -- Andreas, 2013-10-22 call applyDef to make sure we get the original proj.
      -- xs' <- mapM (traverse (`applyDef` defaultArg u)) xs
-}
      reportSDoc "tc.record.eta" 20 $ vcat
        [ text "eta expanding" <+> prettyTCM u <+> text ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ text "tel' =" <+> prettyTCM tel'
          , text "args =" <+> prettyTCM xs'
          ]
        ]
      return (tel', con, xs')

etaExpandAtRecordType :: Type -> Term -> TCM (Telescope, Term)
etaExpandAtRecordType t u = do
  (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType t
  (tel, con, args) <- etaExpandRecord_ r pars def u
  return (tel, Con con args)

-- | The fields should be eta contracted already.
--
--   We can eta contract if all fields @f = ...@ are irrelevant
--   or all fields @f@ are the projection @f v@ of the same value @v@,
--   but we need at least one relevant field to find the value @v@.
--
--   TODO: this can be moved out of TCM (but only if ConHead
--   stores also the Arg-decoration of the record fields.
etaContractRecord :: QName -> ConHead -> Args -> TCM Term
etaContractRecord r c args = do
  Record{ recFields = xs } <- getRecordDef r
  let check :: I.Arg Term -> I.Arg QName -> Maybe (Maybe Term)
      check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (getRelevance a, hasElims $ unArg a) of
          (Irrelevant, _)   -> Just Nothing
          -- if @a@ is the record field name applied to a single argument
          -- then it passes the check
          (_, Just (_, [])) -> Nothing  -- not a projection
          (_, Just (h, es)) | Proj f <- last es, unArg ax == f
                            -> Just $ Just $ h $ init es
          _                 -> Nothing
      fallBack = return (Con c args)
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> do
      reportSDoc "tc.record.eta" 15 $
        text "record constructor is applied to too many arguments: "
          <+> prettyTCM (Con c args)
      __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      case zipWithM check args xs of
        Just as -> case [ a | Just a <- as ] of
          (a:as) ->
            if all (a ==) as
              then do
                reportSDoc "tc.record.eta" 15 $ vcat
                  [ text "record" <+> prettyTCM (Con c args)
                  , text "is eta-contracted to" <+> prettyTCM a
                  ]
                return a
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
  def <- getRecordDef r
  emap (Con $ recConHead def) <$> check (recTel def `apply` ps)
  where
  check :: Telescope -> TCM (Either MetaId (Maybe [I.Arg Term]))
  check EmptyTel            = return $ Right $ Just []
  check (ExtendTel dom tel)
        | isIrrelevant dom && regardIrrelevance =
    underAbstraction dom tel $ \ tel ->
      emap (Arg (domInfo dom) garbage :) <$> check tel
  check (ExtendTel dom tel) = do
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
        Nothing         -> return $ Right Nothing
        Just (r, ps, _) -> do
          emap (abstract tel) <$> isSingletonRecord' regardIrrelevance r ps
{-
    t <- reduceB $ unEl t
    case ignoreSharing <$> t of
      Blocked m _            -> return (Left m)
      NotBlocked (MetaV m _) -> return (Left m)
      NotBlocked (Def r es)  -> do
        let ps = fromMaybe __IMPOSSIBLE $ allApplyElims es
        ifM (isNothing <$> isRecord r) (return $ Right Nothing) $ do
          emap (abstract tel) <$> isSingletonRecord' regardIrrelevance r ps
      _ -> return (Right Nothing)
-}

-- | Auxiliary function.
emap :: (a -> b) -> Either c (Maybe a) -> Either c (Maybe b)
emap = mapRight . fmap
