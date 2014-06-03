module Types.Signature
    ( Signature
    , empty
      -- * Definitions
    , getDefinition
    , addDefinition
      -- * MetaVars
    , MetaInst(..)
    , getMetaInst
    , addFreshMetaVar
    , instantiateMetaVar
    ) where

import qualified Data.Map                         as Map
import qualified Data.Set                         as Set

import           Syntax.Abstract                  (Name)
import           Types.Definition
import           Types.Var
import qualified Types.Telescope                  as Tel
import           Text.PrettyPrint.Extended        (render)

data Signature t = Signature
    { sDefinitions :: Map.Map Name (Definition t)
    , sMetaStore   :: Map.Map MetaVar (MetaInst t)
    }

empty :: Signature t
empty = Signature Map.empty Map.empty

getDefinition :: Signature t -> Name -> Definition t
getDefinition sig name =
    case Map.lookup name (sDefinitions sig) of
      Nothing  -> error $ "impossible.getDefinition: not found " ++ show name
      Just def -> def

addDefinition :: Signature t -> Name -> Definition t -> Signature t
addDefinition sig name def = case def of
    Projection projIx tyCon _ -> addProjection tyCon projIx
    Constructor tyCon _       -> addConstructor tyCon
    _                         -> sig'
  where
    sig' = sig{sDefinitions = Map.insert name def (sDefinitions sig)}

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

data MetaInst t
    = Open (Closed t) -- Type
    | Inst (Closed t) -- Type
           (Closed t) -- Body

getMetaInst :: Signature t -> MetaVar -> MetaInst t
getMetaInst sig name =
    case Map.lookup name (sMetaStore sig) of
      Nothing -> error $ "impossible.getMetaInst: not found " ++ show name
      Just d -> d

addFreshMetaVar :: Signature t -> Closed t -> (MetaVar, Signature t)
addFreshMetaVar sig type_ =
    (mv, sig{sMetaStore = Map.insert mv (Open type_) (sMetaStore sig)})
  where
    mv = case Map.maxViewWithKey (sMetaStore sig) of
        Nothing                  -> MetaVar 0
        Just ((MetaVar i, _), _) -> MetaVar (i + 1)

instantiateMetaVar :: Signature t -> MetaVar -> Closed t -> Signature t
instantiateMetaVar sig mv term =
    sig{sMetaStore = Map.insert mv (Inst type_ term) (sMetaStore sig)}
  where
    type_ = case getMetaInst sig mv of
      Inst _ _   -> error "Types.Signature.instantiateMetaVar: already instantiated"
      Open type' -> type'
