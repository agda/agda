
module Agda.TypeChecking.Datatypes where

import Control.Monad.Except

import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Constructors
---------------------------------------------------------------------------

-- | Get true constructor with record fields.
getConHead :: (HasConstInfo m) => QName -> m (Either SigError ConHead)
getConHead c = runExceptT $ do
  def <- ExceptT $ getConstInfo' c
  case theDef def of
    Constructor { conSrcCon = c' } -> return c'
    Record     { recConHead = c' } -> return c'
    _ -> throwError $ SigUnknown $ prettyShow c ++ " is not a constructor"

isConstructor :: (HasConstInfo m) => QName -> m Bool
isConstructor q = isRight <$> getConHead q

-- | Get true constructor with fields, expanding literals to constructors
--   if possible.
getConForm :: QName -> TCM (Either SigError ConHead)
getConForm c = caseEitherM (getConHead c) (return . Left) $ \ ch -> do
  Con con _ [] <- constructorForm (Con ch ConOCon [])
  return $ Right con

-- | Augment constructor with record fields (preserve constructor name).
--   The true constructor might only surface via 'reduce'.
getOrigConHead :: QName -> TCM (Either SigError ConHead)
getOrigConHead c = mapRight (setConName c) <$> getConHead c

-- | Get the name of the datatype constructed by a given constructor.
--   Precondition: The argument must refer to a constructor
{-# SPECIALIZE getConstructorData :: QName -> TCM QName #-}
getConstructorData :: HasConstInfo m => QName -> m QName
getConstructorData c = do
  def <- getConstInfo c
  case theDef def of
    Constructor{conData = d} -> return d
    _                        -> __IMPOSSIBLE__

-- | Is the datatype of this constructor a Higher Inductive Type?
--   Precondition: The argument must refer to a constructor of a datatype or record.
consOfHIT :: HasConstInfo m => QName -> m Bool
consOfHIT c = do
  d <- getConstructorData c
  def <- theDef <$> getConstInfo d
  case def of
    Datatype {dataPathCons = xs} -> return $ not $ null xs
    Record{} -> return False
    _  -> __IMPOSSIBLE__

isPathCons :: HasConstInfo m => QName -> m Bool
isPathCons c = do
  d <- getConstructorData c
  def <- theDef <$> getConstInfo d
  case def of
    Datatype {dataPathCons = xs} -> return $ c `elem` xs
    Record{} -> return False
    _  -> __IMPOSSIBLE__

-- | @getConType c t@ computes the constructor parameters from type @t@
--   and returns them plus the instantiated type of constructor @c@.
--   This works also if @t@ is a function type ending in a data/record type;
--   the term from which @c@ comes need not be fully applied
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
getConType
  :: PureTCM m
  => ConHead  -- ^ Constructor.
  -> Type     -- ^ Ending in data/record type.
  -> m (Maybe ((QName, Type, Args), Type))
       -- ^ @Nothing@ if not ends in data or record type.
       --
       --   @Just ((d, dt, pars), ct)@ otherwise, where
       --     @d@    is the data or record type name,
       --     @dt@   is the type of the data or record name,
       --     @pars@ are the reconstructed parameters,
       --     @ct@   is the type of the constructor instantiated to the parameters.
getConType c t = do
  reportSDoc "tc.getConType" 30 $ sep $
    [ "getConType: constructor "
    , prettyTCM c
    , " at type "
    , prettyTCM t
    ]
  TelV tel t <- telView t
  -- Now @t@ lives under @tel@, we need to remove the dependency on @tel@.
  -- This will succeed if @t@ is indeed a data/record type that is the
  -- type of a constructor coming from a term
  -- (applied to at least the parameters).
  -- Note: @t@ will have some unbound deBruijn indices if view outside of @tel@.
  reportSLn "tc.getConType" 35 $ "  target type: " ++ prettyShow t
  applySubst (strengthenS impossible (size tel)) <$> do
    addContext tel $ getFullyAppliedConType c t
  -- Andreas, 2017-08-18, issue #2703:
  -- The original code
  --    getFullyAppliedConType c $ applySubst (strengthenS impossible (size tel)) t
  -- crashes because substitution into @Def@s is slightly too strict
  -- (see @defApp@ and @canProject@).
  -- Strengthening the parameters after the call to @getFullyAppliedConType@
  -- does not produce intermediate terms with __IMPOSSIBLE__s and this thus
  -- robust wrt. strictness/laziness of substitution.

-- | @getFullyAppliedConType c t@ computes the constructor parameters
--   from data type @t@ and returns them
--   plus the instantiated type of constructor @c@.
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
--
--   Precondition: @t@ is reduced.
getFullyAppliedConType
  :: PureTCM m
  => ConHead  -- ^ Constructor.
  -> Type     -- ^ Reduced type of the fully applied constructor.
  -> m (Maybe ((QName, Type, Args), Type))
       -- ^ @Nothing@ if not data or record type.
       --
       --   @Just ((d, dt, pars), ct)@ otherwise, where
       --     @d@    is the data or record type name,
       --     @dt@   is the type of the data or record name,
       --     @pars@ are the reconstructed parameters,
       --     @ct@   is the type of the constructor instantiated to the parameters.
getFullyAppliedConType c t = do
  reportSLn "tc.getConType" 35 $ unwords $
    [ "getFullyAppliedConType", prettyShow c, prettyShow t ]
  c <- fromRight __IMPOSSIBLE__ <$> do getConHead $ conName c
  case unEl t of
    -- Note that if we come e.g. from getConType,
    -- then the non-parameter arguments of @es@ might contain __IMPOSSIBLE__
    -- coming from strengthening.  (Thus, printing them is not safe.)
    Def d es -> do
      reportSLn "tc.getConType" 35 $ unwords $
        [ "getFullyAppliedConType: case Def", prettyShow d, prettyShow es ]
      def <- getConstInfo d
      let cont n = do
            -- At this point we can be sure that the parameters are well-scoped.
            let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take n es
            Just . ((d, defType def, pars),) <$> do
              (`piApplyM` pars) . defType =<< getConInfo c
      case theDef def of
        Datatype { dataPars = n, dataCons   = cs  } | conName c `elem` cs -> cont n
        Record   { recPars  = n, recConHead = con } | c == con            -> cont n
        _ ->  return Nothing
    _ -> return Nothing

data ConstructorInfo
  = DataCon Nat
      -- ^ Arity.
  | RecordCon PatternOrCopattern HasEta [Dom QName]
      -- ^ List of field names.

-- | Return the number of non-parameter arguments to a data constructor,
--   or the field names of a record constructor.
--
--   For getting just the arity of constructor @c@,
--   use @either id size <$> getConstructorArity c@.
getConstructorInfo :: HasConstInfo m => QName -> m ConstructorInfo
getConstructorInfo c = fromMaybe __IMPOSSIBLE__ <$> getConstructorInfo' c

getConstructorInfo' :: HasConstInfo m => QName -> m (Maybe ConstructorInfo)
getConstructorInfo' c = do
  (theDef <$> getConstInfo c) >>= \case
    Constructor{ conData = d, conArity = n } -> Just <$> do
      (theDef <$> getConstInfo d) >>= \case
        r@Record{ recFields = fs } ->
           return $ RecordCon (recPatternMatching r) (recEtaEquality r) fs
        Datatype{} ->
           return $ DataCon n
        _ -> __IMPOSSIBLE__
    _ -> return Nothing

---------------------------------------------------------------------------
-- * Data types
---------------------------------------------------------------------------

-- | Check if a name refers to a datatype or a record with a named constructor.
isDatatype :: QName -> TCM Bool
isDatatype d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{}                   -> return True
    Record{recNamedCon = namedC} -> return namedC
    _                            -> return False

-- | Check if a name refers to a datatype or a record.
isDataOrRecordType :: QName -> TCM (Maybe DataOrRecord)
isDataOrRecordType d = do
  (theDef <$> getConstInfo d) >>= \case
    Record{ recPatternMatching } -> return $ Just $ IsRecord recPatternMatching
    Datatype{} -> return $ Just IsData
    _          -> return $ Nothing

-- | Precodition: 'Term' is 'reduce'd.
isDataOrRecord :: Term -> TCM (Maybe QName)
isDataOrRecord = \case
    Def d _ -> fmap (const d) <$> isDataOrRecordType d
    _       -> return Nothing

getNumberOfParameters :: HasConstInfo m => QName -> m (Maybe Nat)
getNumberOfParameters d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = n }   -> return $ Just n
    Record{ recPars = n }      -> return $ Just n
    Constructor{ conPars = n } -> return $ Just n
    _                          -> return Nothing

-- | This is a simplified version of @isDatatype@ from @Coverage@,
--   useful when we do not want to import the module.
getDatatypeArgs :: HasConstInfo m => Type -> m (Maybe (QName, Args, Args))
getDatatypeArgs t = do
  case unEl t of
    Def d es -> do
      let ~(Just args) = allApplyElims es
      def <- theDef <$> getConstInfo d
      case def of
        Datatype{dataPars = np} -> do
          let !(ps, is) = splitAt np args
          return $ Just (d,   ps, is)
        Record{} -> do
          return $ Just (d, args, [])
        _ -> return Nothing
    _ -> return Nothing

getNotErasedConstructors :: QName -> TCM [QName]
getNotErasedConstructors d = do
  cs <- getConstructors d
  flip filterM cs $ \ c -> do
    usableModality <$> getConstInfo c

-- | Precondition: Name is a data or record type.
getConstructors :: QName -> TCM [QName]
getConstructors d = fromMaybe __IMPOSSIBLE__ <$>
  getConstructors' d

-- | 'Nothing' if not data or record type name.
getConstructors' :: QName -> TCM (Maybe [QName])
getConstructors' d = getConstructors_ . theDef <$> getConstInfo d

-- | 'Nothing' if not data or record definition.
getConstructors_ :: Defn -> Maybe [QName]
getConstructors_ = \case
    Datatype{dataCons = cs} -> Just cs
    Record{recConHead = h}  -> Just [conName h]
    _                       -> Nothing
