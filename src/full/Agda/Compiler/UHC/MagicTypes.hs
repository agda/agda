{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-- | Defines some magic builtin datatypes.
module Agda.Compiler.UHC.MagicTypes
(   builtinUnitCtor
  , MagicName
  , getMagicTypes
  , MagicConstrInfo
  , MagicTypeInfo
  )
where

import Data.List
import qualified Data.Map as M

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Bridge


-- | name of a magic, differently translated datatype/constructor
type MagicName = String


type MagicConstrInfo = M.Map MagicName CTag -- maps primitive names to constructor ctags
type MagicTypeInfo = M.Map MagicName (Maybe HsName, MagicConstrInfo) -- maps types to the UHC Core name
-- (or nothing for unit) and to their constructors.

getMagicTypes :: MagicTypeInfo
getMagicTypes = M.fromList $ map f (primCrTys1 ++ primAgdaTys1)
  where f :: (MagicName, [(MagicName, CTag)]) -> (MagicName, (Maybe HsName, MagicConstrInfo))
        f (dtMgcNm, constrs) = let dtCrNm = ctagDataTyNm $ snd $ head constrs
                                in (dtMgcNm, (dtCrNm, M.fromList constrs))
-- | Returns the name of the datatype or 'Nothing' for the unit datatype.
ctagDataTyNm :: CTag -> Maybe HsName
ctagDataTyNm = destructCTag Nothing (\dt _ _ _ -> Just dt)


-- Implementation of Nat might change later, we may want to optimize Nat in the future
primAgdaTys1 :: [(MagicName -- see primCrTys1
    , [(MagicName, CTag)]
    )]
primAgdaTys1 = map fixConstrs
          [ ("NAT", "UHC.Agda.Builtins.Nat",
                [ ("SUC",  "Suc", 0, 1)
                , ("ZERO", "Zero", 1, 0)
                ])
          ]
  where fixConstrs :: (MagicName, String, [(MagicName, String, Int, Int)]) -> (MagicName, [(MagicName, CTag)])
        fixConstrs (dtMagic, dtCrNm, constrs) = (dtMagic, [ (conMagic, mkCTag (mkHsName1 dtCrNm) (mkHsCtorNm dtCrNm conCrNm ) tag arity) | (conMagic, conCrNm, tag, arity) <- constrs ])
        mkHsCtorNm :: String -> String -> HsName
        mkHsCtorNm dt con = mkHsName1 ((dropWhileEnd (/='.') dt) ++ con)


primCrTys1 :: [(
      MagicName    -- the magic name of the dt in COMPILED_CORE_DATA pragmas
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
