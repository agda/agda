{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Defines UHC Core functions used in other parts of Agda.
-- E.g. parsing Core pragmas uses the `parseCoreCode` function.
module Agda.Compiler.UHC.Pragmas.Parse
  ( module Agda.Compiler.UHC.Pragmas.Base
  , parseCoreExpr
  , coreExprToCExpr
  , parseCoreData
  , parseCoreConstrs
  )

where


import Data.List
import qualified Data.Map as M

import Agda.TypeChecking.Monad
import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.MagicTypes

import Agda.Compiler.UHC.Bridge as CA

#include "undefined.h"
import Agda.Utils.Impossible

-- | Parse a COMPILED_DATA_UHC specification.
parseCoreData :: MonadTCM m => String -> m CoreType
parseCoreData dt = do
  isDtMgc <- isMagicEntity getMagicTypes dt "datatype"
  return $ case isDtMgc of
    Nothing         -> CTNormal dt
    Just (dtMgc, _) -> CTMagic dtMgc

parseCoreConstrs :: MonadTCM m => CoreType -> [String] -> m [CoreConstr]
parseCoreConstrs (CTNormal dtCrNm) cs = do
  constrs <- mapM parseNormalConstr cs
  -- UHC assigns tags in lexographical order.
  -- Requires that the mapping is complete, else it will break.
  return $ zipWith setTag (sortBy ccOrd constrs) [0..]
    where
        parseNormalConstr :: MonadTCM m => String -> m CoreConstr
        parseNormalConstr c
            | isMagic c =  typeError $
                GenericError $ "Magic constructor " ++ (drop 2 $ init $ init c) ++ " can only be used for magic datatypes."
            | otherwise = let dtMod = dropWhileEnd (/='.') dtCrNm
                              conNm = dtMod ++ c
                           -- tag gets assigned after we have parsed all ctors
                           in return $ CCNormal (mkHsName1 dtCrNm) (mkHsName1 conNm) __IMPOSSIBLE__
        ccOrd :: CoreConstr -> CoreConstr -> Ordering
        ccOrd (CCNormal dtNm1 ctNm1 _) (CCNormal dtNm2 ctNm2 _) | dtNm1 == dtNm2 = compare ctNm1 ctNm2
        ccOrd _ _ = __IMPOSSIBLE__

parseCoreConstrs (CTMagic dtMgcNm) cs = do
  mapM parseMagicConstr cs
    where
        (_, conMp) = getMagicTypes M.! dtMgcNm
        parseMagicConstr :: MonadTCM m => String ->  m CoreConstr
        parseMagicConstr c
            | not (isMagic c) = typeError $
                GenericError $ "A magic datatype can only have magic constructors."
            | otherwise = do
                (Just (conMgcNm, _)) <- isMagicEntity conMp c "constructor"
                return $ CCMagic dtMgcNm conMgcNm


-- | Parse a COMPILED_UHC expression.
parseCoreExpr :: String -> Either String CoreExpr
#if defined(UHC_BACKEND)
parseCoreExpr str = either Left (const $ Right str) (coreExprToCExpr str)
#else
-- we don't have the uhc-light parser, so just succeed here.
parseCoreExpr str = Right str
#endif

coreExprToCExpr :: CoreExpr -> Either String CExpr
#if defined(UHC_BACKEND)
coreExprToCExpr str = case CA.parseExpr defaultEHCOpts str of
    (Left errs) -> Left $ intercalate "\n" errs
    (Right res) -> Right res
#else
coreExprToCExpr = __IMPOSSIBLE__
#endif

-- | Check if the given name is a valid Magic entity.
isMagicEntity :: MonadTCM m
    => M.Map MagicName a    -- ^ lookup table
    -> String   -- ^ name to lookup.
    -> String   -- ^ type of the entity. Used for errors messages.
    -> m (Maybe (String, a))
isMagicEntity tbl xs ty | isMagic xs =
  case nm `M.lookup` tbl of
    Just x -> return $ Just (nm, x)
    Nothing -> typeError $ GenericError $ "No magic " ++ ty ++ " with the name " ++ nm ++ " exists."
  where nm = init $ init $ drop 2 xs
isMagicEntity _ _ _ | otherwise = return Nothing

-- | Checks if the given name is syntactically a Magic name.
-- A syntactally correct magic name is NOT necessarily a valid magic name.
isMagic :: String -> Bool
isMagic xs = "__" `isPrefixOf` xs && "__" `isSuffixOf` xs
