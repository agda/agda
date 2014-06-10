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
import           Types.Var
import           Text.PrettyPrint.Extended        (render)
import           Types.Term                       hiding (metaVars)

data Signature t = Signature
    { sDefinitions :: Map.Map Name (Closed (Definition t))
    , sMetasTypes  :: Map.Map MetaVar (Closed (Type t))
    , sMetasBodies :: Map.Map MetaVar (Closed (Term t))
    }

empty :: Signature t
empty = Signature Map.empty Map.empty Map.empty

getDefinition :: Signature t -> Name -> Closed (Definition t)
getDefinition sig name =
    case Map.lookup name (sDefinitions sig) of
      Nothing   -> error $ "impossible.getDefinition: not found " ++ show name
      Just def' -> def'

addDefinition :: Signature t -> Name -> Closed (Definition t) -> Signature t
addDefinition sig name def' = case def' of
    Projection projIx tyCon _ -> addProjection tyCon projIx
    Constructor tyCon _       -> addConstructor tyCon
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

    addConstructor tyCon = case getDefinition sig' tyCon of
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

getMetaVarType :: Signature t -> MetaVar -> Closed (Type t)
getMetaVarType sig mv =
    case Map.lookup mv (sMetasTypes sig) of
      Nothing -> error $ "impossible.getMetaVarType: not found " ++ show mv
      Just d -> d

getMetaVarBody :: Signature t -> MetaVar -> Maybe (Closed (Term t))
getMetaVarBody sig mv = Map.lookup mv (sMetasBodies sig)

-- TODO more assertions in the two functions below.

addMetaVar :: Signature t -> Closed t -> (MetaVar, Signature t)
addMetaVar sig type_ =
    (mv, sig{sMetasTypes = Map.insert mv type_ (sMetasTypes sig)})
  where
    mv = case Map.maxViewWithKey (sMetasTypes sig) of
        Nothing                  -> MetaVar 0
        Just ((MetaVar i, _), _) -> MetaVar (i + 1)

instantiateMetaVar :: Signature t -> MetaVar -> Closed t -> Signature t
instantiateMetaVar sig mv term =
    sig{sMetasBodies = Map.insert mv term (sMetasBodies sig)}

metaVarsTypes :: Signature t -> Map.Map MetaVar (Closed (Type t))
metaVarsTypes = sMetasTypes

metaVarsBodies :: Signature t -> Map.Map MetaVar (Closed (Term t))
metaVarsBodies = sMetasBodies
