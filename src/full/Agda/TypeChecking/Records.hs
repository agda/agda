{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Records where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Function

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Datatypes
import Agda.Utils.List
import Agda.Utils.Monad

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
--   does not refer to a record.
getRecordDef :: QName -> TCM Defn
getRecordDef r = do
  def <- theDef <$> getConstInfo r
  case def of
    Record{} -> return def
    _        -> typeError $ ShouldBeRecordType (El Prop $ Def r [])

-- | Get the field names of a record.
getRecordFieldNames :: QName -> TCM [Arg C.Name]
getRecordFieldNames r =
  map (fmap (nameConcrete . qnameName)) . recFields <$> getRecordDef r

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs <- (Map.union `on` sigDefinitions) <$> getSignature <*> getImportedSignature
  let possible def = case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given inrecord
          where inrecord = Set.fromList $ map (nameConcrete . qnameName . unArg) fs
        _ -> False
  return [ defName d | d <- Map.elems defs, possible d ]
  where
    given = Set.fromList fields

-- | Get the field types of a record.
getRecordFieldTypes :: QName -> TCM Telescope
getRecordFieldTypes r = recTel <$> getRecordDef r

-- | Get the type of the record constructor.
getRecordConstructorType :: QName -> TCM Type
getRecordConstructorType r = recConType <$> getRecordDef r

-- | Returns the given record type's constructor name (with an empty
-- range).
getRecordConstructor :: QName -> TCM QName
getRecordConstructor r = killRange <$> recCon <$> getRecordDef r

-- | Check if a name refers to a record.
isRecord :: QName -> TCM Bool
isRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{} -> True
    _        -> False

-- | Check if a name refers to an eta expandable record.
isEtaRecord :: QName -> TCM Bool
isEtaRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{recEtaEquality = eta} -> eta
    _                            -> False

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: Type -> TCM (Maybe (QName, Args))
isEtaRecordType (El _ (Def d ps)) = ifM (isEtaRecord d) (return $ Just (d, ps)) (return Nothing)
isEtaRecordType _ = return Nothing

-- | Check if a name refers to a record constructor.
isRecordConstructor :: QName -> TCM Bool
isRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> isRecord r
    _                          -> return False

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

{-| Compute the eta expansion of a record. The first argument should be
    the name of a record type. Given

    @record R : Set where x : A; y : B; .z : C@

    and @r : R@, @etaExpand R [] r@ is @[R.x r, R.y r, DontCare]@
-}
etaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord r pars u = do
  Record{ recFields = xs, recTel = tel } <- getRecordDef r
  let tel' = apply tel pars
  case u of
    Con _ args -> return (tel', args)  -- Already expanded.
    _          -> do
      -- irrelevant fields are expanded to DontCare
      -- this is sound because etaExpandRecord is only called during conversion
      -- WARNING: do not use etaExpandRecord to expand MetaVars!!
      let proj (Arg h Irrelevant _) = Arg h Irrelevant $ DontCare Nothing
          proj (Arg h rel x)        = Arg h rel $
            Def x [defaultArg u]
      reportSDoc "tc.record.eta" 20 $ vcat
        [ text "eta expanding" <+> prettyTCM u <+> text ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ text "tel' =" <+> prettyTCM tel'
          , text "args =" <+> prettyTCM (map proj xs)
          ]
        ]
      return (tel', map proj xs)
  where
    hide a = a { argHiding = Hidden }

-- | The fields should be eta contracted already.
etaContractRecord :: QName -> QName -> Args -> TCM Term
etaContractRecord r c args = do
  Record{ recPars = npars, recFields = xs } <- getRecordDef r
  let check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (argRelevance a, unArg a) of
          (Irrelevant, _) -> return $ Just $ DontCare Nothing
          -- if @a@ is the record field name applied to a single argument
          -- then it passes the check
          (_, Def y [arg]) | unArg ax == y
                         -> return (Just $ unArg arg)
          _              -> return Nothing
      fallBack = return (Con c args)
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      as <- zipWithM check args xs
      case sequence as of
        Just as -> case filter notDontCare as of
          (a:as) ->
            if all (a ==) as
              then do
                reportSDoc "tc.record.eta" 15 $ vcat
                  [ text "record" <+> prettyTCM (Con c args)
                  , text "is eta-contracted to" <+> prettyTCM a
                  ]
                return a
              else fallBack
          _ -> fallBack -- just DontCares
        _ -> fallBack  -- a Nothing
  where notDontCare (DontCare _) = False
        notDontCare _            = True

-- | Is the type a hereditarily singleton record type? May return a
-- blocking metavariable.
--
-- Precondition: The name should refer to a record type, and the
-- arguments should be the parameters to the type.

isSingletonRecord :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecord = isSingletonRecord' False

isSingletonRecordModuloRelevance :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecordModuloRelevance = isSingletonRecord' True

isSingletonRecord' :: Bool -> QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecord' regardIrrelevance r ps =
  check =<< ((`apply` ps) <$> getRecordFieldTypes r)
  where
  check EmptyTel            = return (Right True)
  check (ExtendTel arg tel) | regardIrrelevance && argRelevance arg == Irrelevant =
    underAbstraction arg tel check
  check (ExtendTel arg tel) = do
    TelV _ t <- telView $ unArg arg
    t <- reduceB $ unEl t
    case t of
      Blocked m _            -> return (Left m)
      NotBlocked (MetaV m _) -> return (Left m)
      NotBlocked (Def r ps)  ->
        ifM (not <$> isRecord r) (return $ Right False) $ do
          isRec <- isSingletonRecord' regardIrrelevance r ps
          case isRec of
            Left _      -> return isRec
            Right False -> return isRec
            Right True  -> underAbstraction arg tel $ check
      _ -> return (Right False)
