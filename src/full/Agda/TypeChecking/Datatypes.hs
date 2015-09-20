{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Datatypes where

import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute

import Agda.Utils.Size
import Agda.Utils.Functor

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Constructors
---------------------------------------------------------------------------

-- | Get true constructor with record fields.
getConHead :: QName -> TCM ConHead
getConHead c = conSrcCon . theDef <$> getConstInfo c

-- | Get true constructor as term.
getConTerm :: QName -> TCM Term
getConTerm c = flip Con [] <$> getConHead c

-- | Get true constructor with fields, expanding literals to constructors
--   if possible.
getConForm :: QName -> TCM ConHead
getConForm c = do
  Con con [] <- ignoreSharing <$> do constructorForm =<< getConTerm c
  return con

-- | Augment constructor with record fields (preserve constructor name).
--   The true constructor might only surface via 'reduce'.
getOrigConHead :: QName -> TCM ConHead
getOrigConHead c = setConName c <$> getConHead c

-- | Analogous to 'getConTerm'.
getOrigConTerm :: QName -> TCM Term
getOrigConTerm c = flip Con [] <$> getOrigConHead c

-- | Get the name of the datatype constructed by a given constructor.
--   Precondition: The argument must refer to a constructor
{-# SPECIALIZE getConstructorData :: QName -> TCM QName #-}
getConstructorData :: HasConstInfo m => QName -> m QName
getConstructorData c = do
  def <- getConstInfo c
  case theDef def of
    Constructor{conData = d} -> return d
    _                        -> __IMPOSSIBLE__

-- | @getConType c t@ computes the constructor parameters from type @t@
--   and returns the instantiated type of constructor @c@.
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
--   Precondition: @t@ is reduced.
getConType :: ConHead -> Type -> TCM (Maybe Type)
getConType c t = do
  c <- getConHead $ conName c
  case ignoreSharing $ unEl t of
    Def d es -> do
      def <- theDef <$> getConstInfo d
      case def of
        Datatype { dataPars = n, dataCons   = cs  } | conName c `elem` cs -> cont n
        Record   { recPars  = n, recConHead = con } | c == con            -> cont n
        _ ->  return Nothing
      where
        cont n = do
          let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take n es
          Just . (`apply` pars) . defType <$> getConInfo c
    _ -> return Nothing

data HasEta = NoEta | YesEta
  deriving (Eq)

data ConstructorInfo = DataCon Nat  -- arity
                     | RecordCon HasEta [I.Arg QName]

-- | Return the number of non-parameter arguments to a data constructor,
--   or the field names of a record constructor.
--
--   For getting just the arity of constructor @c@,
--   use @either id size <$> getConstructorArity c@.
getConstructorInfo :: QName -> TCM ConstructorInfo
getConstructorInfo c = do
  Defn{ defType = t, theDef = def } <- getConstInfo c
  case def of
    Constructor{ conData = d, conPars = n } -> do
      def <- theDef <$> getConstInfo d
      case def of
        r@Record{ recFields = fs } ->
           return $ RecordCon (if recEtaEquality r then YesEta else NoEta) fs
        Datatype{} -> do
          -- TODO: I do not want to take the type of constructor apart
          -- to see its arity!
          TelV tel _ <- telView t
          return $ DataCon $ size tel - n
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

getConstructorArity :: QName -> TCM Nat
getConstructorArity c =
  for (getConstructorInfo c) $ \i ->
  case i of
    DataCon n      -> n
    RecordCon _ fs -> size fs

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

data DataOrRecord = IsData | IsRecord
  deriving (Eq, Ord, Show)

-- | Check if a name refers to a datatype or a record.
isDataOrRecordType :: QName -> TCM (Maybe DataOrRecord)
isDataOrRecordType d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{} -> return $ Just IsData
    Record{}   -> return $ Just IsRecord
    _          -> return $ Nothing

-- | Precodition: 'Term' is 'reduce'd.
isDataOrRecord :: Term -> TCM (Maybe QName)
isDataOrRecord v = do
  case ignoreSharing v of
    Def d _ -> fmap (const d) <$> isDataOrRecordType d
    _       -> return Nothing

getNumberOfParameters :: QName -> TCM (Maybe Nat)
getNumberOfParameters d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = n }   -> return $ Just n
    Record{ recPars = n }      -> return $ Just n
    Constructor{ conPars = n } -> return $ Just n
    _                          -> return Nothing

{- UNUSED
data DatatypeInfo = DataInfo
  { datatypeName   :: QName
  , datatypeParTel :: Telescope
  , datatypePars   :: Args
  , datatypeIxTel  :: Telescope
  , datatypeIxs    :: Args
  }

-- | Get the name and parameters from a type if it's a datatype or record type
--   with a named constructor.
getDatatypeInfo :: Type -> TCM (Maybe DatatypeInfo)
getDatatypeInfo t = do
  t <- reduce t
  case unEl t of
    Def d args -> do
      n          <- getDefFreeVars d
      args       <- return $ genericDrop n args
      def        <- instantiateDef =<< getConstInfo d
      TelV tel _ <- telView (defType def)
      let npars  = case theDef def of
            Datatype{dataPars = np} -> Just np
            Record{recPars = np, recNamedCon = True}
              | genericLength args == np -> Just np
              | otherwise                -> __IMPOSSIBLE__
            _                            -> Nothing
      return $ do
        np <- npars
        let (pt, it) = genericSplitAt np $ telToList tel
            parTel   = telFromList pt
            ixTel    = telFromList it
            (ps, is) = genericSplitAt np args
        return $ DataInfo { datatypeName = d
                          , datatypeParTel = parTel
                          , datatypePars   = ps
                          , datatypeIxTel  = ixTel
                          , datatypeIxs    = is
                          }
    _ -> return Nothing
-}
