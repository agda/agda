module Types.Signature
    ( Signature
    , empty
      -- * Definitions
    , getDefinition
    , addDefinition
      -- * MetaVars
    , getMetaVarType
    , getMetaVarBody
    , addMetaVar
    , instantiateMetaVar
    , metaVarsTypes
    , metaVarsBodies
    ) where

import qualified Data.Map                         as Map

import           Syntax.Abstract                  (Name)
import           Types.Definition
import           Text.PrettyPrint.Extended        (render)
import           Types.Term

-- | A 'Signature' stores every globally scoped thing.  That is,
-- 'Definition's and 'MetaVar's bodies and types.
data Signature t = Signature
    { sDefinitions :: Map.Map Name (Closed (Definition t))
    , sMetasTypes  :: Map.Map MetaVar (Closed (Type t))
    , sMetasBodies :: Map.Map MetaVar (Closed (Term t))
    -- ^ INVARIANT: Every 'MetaVar' in 'sMetaBodies' is also in
    -- 'sMetasTypes'.
    }

empty :: Signature t
empty = Signature Map.empty Map.empty Map.empty

-- | Gets a definition for the given name.  Fails if no definition can
-- be found.
getDefinition :: Signature t -> Name -> Closed (Definition t)
getDefinition sig name =
    case Map.lookup name (sDefinitions sig) of
      Nothing   -> error $ "impossible.getDefinition: not found " ++ show name
      Just def' -> def'

-- | Adds a new definition.
--
-- In the case of a new 'Projection' or 'DataCon', the definition of the
-- type constructor will be updated with the new information.  Fails if
-- the definition for the type constructor is not present.
addDefinition :: Signature t -> Name -> Closed (Definition t) -> Signature t
addDefinition sig name def' = case def' of
    Projection projIx tyCon _ -> addProjection tyCon projIx
    DataCon tyCon _           -> addDataCon tyCon
    _                         -> sig'
  where
    sig' = sig{sDefinitions = Map.insert name def' (sDefinitions sig)}

    addProjection tyCon projIx = case getDefinition sig' tyCon of
      Constant (Record dataCon projs) tyConType ->
        let projs' = projs ++ [(name, projIx)]
            defs   = Map.insert tyCon (Constant (Record dataCon projs') tyConType) (sDefinitions sig')
        in sig'{sDefinitions = defs}
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a record"

    addDataCon tyCon = case getDefinition sig' tyCon of
      Constant (Data dataCons) tyConType ->
        let dataCons' = dataCons ++ [name]
            defs      = Map.insert tyCon (Constant (Data dataCons') tyConType) (sDefinitions sig')
        in sig'{sDefinitions = defs}
      Constant (Record dataCon _) _ ->
        if name == dataCon
        then sig'
        else error $ "impossible.addDefinition: mismatching constructors " ++
                     render name ++ " and " ++ render dataCon
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a data type"

-- | Gets the type of a 'MetaVar'.  Fails if the 'MetaVar' if not
-- present.
getMetaVarType :: Signature t -> MetaVar -> Closed (Type t)
getMetaVarType sig mv =
    case Map.lookup mv (sMetasTypes sig) of
      Nothing -> error $ "impossible.getMetaVarType: not found " ++ show mv
      Just d -> d

-- | Gets the body of a 'MetaVar', if present.
getMetaVarBody :: Signature t -> MetaVar -> Maybe (Closed (Term t))
getMetaVarBody sig mv = Map.lookup mv (sMetasBodies sig)

-- | Creates a new 'MetaVar' with the provided type.
addMetaVar :: Signature t -> Closed (Type t) -> (MetaVar, Signature t)
addMetaVar sig type_ =
    (mv, sig{sMetasTypes = Map.insert mv type_ (sMetasTypes sig)})
  where
    mv = case Map.maxViewWithKey (sMetasTypes sig) of
        Nothing                  -> MetaVar 0
        Just ((MetaVar i, _), _) -> MetaVar (i + 1)

-- | Instantiates the given 'MetaVar' with the given body.  Fails if no
-- type is present for the 'MetaVar'.
instantiateMetaVar :: Signature t -> MetaVar -> Closed (Term t) -> Signature t
instantiateMetaVar sig mv _ | not (Map.member mv (sMetasTypes sig)) =
  error $ "impossible.instantiateMetaVar: " ++ show mv ++ " not present."
instantiateMetaVar sig mv term =
  sig{sMetasBodies = Map.insert mv term (sMetasBodies sig)}

-- | Gets the types of all 'MetaVar's.
metaVarsTypes :: Signature t -> Map.Map MetaVar (Closed (Type t))
metaVarsTypes = sMetasTypes

-- | Gets the bodies for the instantiated 'MetaVar's.
metaVarsBodies :: Signature t -> Map.Map MetaVar (Closed (Term t))
metaVarsBodies = sMetasBodies
