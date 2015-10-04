{-# LANGUAGE CPP #-}
-- | Defines some magic builtin datatypes.
module Agda.Compiler.UHC.MagicTypes
(   builtinUnitCtor
  , MagicName
  , getMagicTypes
  , MagicConstrInfo
  , MagicTypeInfo
  , HsDataType (..)
  )
where

import Data.List
import qualified Data.Map as M

import Agda.Compiler.UHC.Bridge


-- | name of a magic, differently translated datatype/constructor
type MagicName = String

data HsDataType
  = HsDataType HsName
  | HsUnit

type MagicConstrInfo = M.Map MagicName CTag -- maps primitive names to constructor ctags
type MagicTypeInfo = M.Map MagicName (HsDataType, MagicConstrInfo) -- maps types to the UHC Core name
-- (or nothing for unit) and to their constructors.

getMagicTypes :: MagicTypeInfo
getMagicTypes = M.fromList $ map f primCrTys1
  where f :: (MagicName, [(MagicName, CTag)]) -> (MagicName, (HsDataType, MagicConstrInfo))
        f (dtMgcNm, constrs) = let dtCrNm = ctagDataTyNm $ snd $ head constrs
                                in (dtMgcNm, (dtCrNm, M.fromList constrs))

-- | Returns the name of the datatype or 'Nothing' for the unit datatype.
ctagDataTyNm :: CTag -> HsDataType
ctagDataTyNm = destructCTag HsUnit (\dt _ _ _ -> HsDataType dt)


primCrTys1 :: [(
      MagicName    -- the magic name of the dt in COMPILED_DATA_UHC pragmas
    , [(MagicName, CTag)] -- constructors. Maps magic name to constructor tags.
    )]
primCrTys1 =
          [( "BOOL",
                [ ("TRUE",   ctagTrue defaultEHCOpts)
                , ("FALSE",  ctagFalse defaultEHCOpts)
                ])
          , ("LIST",
                [ ("NIL",  ctagNil defaultEHCOpts)
                , ("CONS", ctagCons defaultEHCOpts)
                ])
          , ("UNIT",
                [("UNIT", ctagUnit)])
          ]

builtinUnitCtor :: HsName
builtinUnitCtor = mkHsName1 "UHC.Agda.Builtins.unit"
