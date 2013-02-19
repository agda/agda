{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Datatypes where

import Control.Applicative ((<$>))
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute

import Agda.Utils.Size
import Agda.Utils.Impossible
#include "../undefined.h"

-- | Get the name of the datatype constructed by a given constructor.
--   Precondition: The argument must refer to a constructor
getConstructorData :: QName -> TCM QName
getConstructorData c = do
  def <- getConstInfo c
  case theDef def of
    Constructor{conData = d} -> return d
    _                        -> __IMPOSSIBLE__


-- | Return the number of non-parameter arguments to a data constructor,
--   or the field names of a record constructor.
--
--   For getting just the arity of constructor @c@,
--   use @either id size <$> getConstructorArity c@.
getConstructorArity :: QName -> TCM (Either Nat [I.Arg QName])
getConstructorArity c = do
  Defn{ defType = t, theDef = def } <- getConstInfo c
  case def of
    Constructor{ conData = d, conPars = n } -> do
      def <- theDef <$> getConstInfo d
      case def of
        Record{ recFields = fs } ->
           return $ Right fs
        Datatype{} -> do
          -- TODO: I do not want to take the type of constructor apart
          -- to see its arity!
          TelV tel _ <- telView t
          return $ Left $ size tel - n
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__


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

isDataOrRecord :: Term -> TCM (Maybe QName)
isDataOrRecord (Def d _)  = fmap (const d) <$> isDataOrRecordType d
isDataOrRecord (Shared p) = isDataOrRecord (derefPtr p)
isDataOrRecord _          = return Nothing

getNumberOfParameters :: QName -> TCM (Maybe Nat)
getNumberOfParameters d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = n} -> return $ Just n
    Record{ recPars = n}    -> return $ Just n
    _                       -> return Nothing

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
