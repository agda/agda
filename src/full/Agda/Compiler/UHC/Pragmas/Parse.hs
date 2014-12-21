{-# LANGUAGE CPP, DeriveDataTypeable #-}
-- | Defines UHC Core functions used in other parts of Agda.
-- E.g. parsing Core pragmas uses the `parseCoreCode` function.
module Agda.Compiler.UHC.Pragmas.Parse
  ( module Agda.Compiler.UHC.Pragmas.Base
  , parseCoreExpr
  , printCoreExpr
  , parseCoreData
  )

where


import Data.Maybe
import Data.List
import Data.List (intercalate)
import Data.Typeable
import qualified Data.Map as M

import Agda.TypeChecking.Monad
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.Builtins

import UHC.Light.Compiler.Core.API as CA

import UHC.Util.ParseUtils
import UHC.Util.Pretty
import UHC.Util.ScanUtils
import UU.Scanner.Position

#include "undefined.h"
import Agda.Utils.Impossible

parseCoreData :: MonadTCM m => String -> [String] -> m (CoreType, [CoreConstr])
parseCoreData dt css = do
  let mgcTys = getMagicTypes
  isDtMgc <- isMagicEntity mgcTys dt "datatype"
  case isDtMgc of
    Nothing -> do
                let dtCrNm = Just $ mkHsName1 dt
                constrs <- mapM (parseConstr Nothing dtCrNm) css
                return (CTNormal dtCrNm, constrs)
    Just (mgcNm, (dtCrNm, constrMp)) -> do
                constrs <- mapM (parseConstr (Just constrMp) dtCrNm) css
                return (CTMagic dtCrNm mgcNm, constrs)

  where parseConstr :: MonadTCM m => Maybe MagicConstrInfo -> CoreTypeName -> String -> m CoreConstr
        parseConstr Nothing _ cs | isMagic cs = typeError $ GenericError $ "Primitive constructor " ++ (drop 2 $ init $ init cs) ++ " can only be used for primitive datatypes."
        parseConstr Nothing dtCrNm cs | "(" `isPrefixOf` cs && ")" `isSuffixOf` cs
                    = let dtCrNm' = fromMaybe __IMPOSSIBLE__ dtCrNm
                          s = tail $ init cs
                          (s1, s2) = splitAt (fromJust $ elemIndex ',' s) s
                       in return $ CCNormal dtCrNm' (mkHsName1 s1) (read s2)
        parseConstr Nothing _ _ | otherwise = typeError $ GenericError $ "Could not parse constructor specification."
        parseConstr (Just _) _ cs | not (isMagic cs) = typeError $ GenericError $ "A primitive datatype can only have primitive constructors."
        parseConstr (Just mp) _ cs | otherwise = do
                (Just (nm, ctg)) <- isMagicEntity mp cs "constructor"
                return $ CCMagic ctg

parseCoreExpr :: String -> Either String CoreExpr
parseCoreExpr str = case CA.parseExpr defaultEHCOpts str of
    (Left errs) -> Left $ intercalate "\n" errs
    (Right res) -> Right res

printCoreExpr :: CoreExpr -> String
printCoreExpr e = disp (pp e) 200 ""

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

isMagic :: String -> Bool
isMagic xs = "__" `isPrefixOf` xs && "__" `isSuffixOf` xs
