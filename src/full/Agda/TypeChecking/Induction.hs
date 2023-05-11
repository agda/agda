module Agda.TypeChecking.Induction where

import Control.Monad

import qualified Data.Set as Set
import Data.Foldable
import Data.Maybe

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad

import Agda.Syntax.Internal

computeInductiveArgs :: [QName] -> TCM ()
computeInductiveArgs qns = do
  reportSDoc "tc.induction" 30 $ prettyTCM qns
  data_names <- Set.fromList <$> filterM (fmap isJust . ignoreAbstractMode . isDataOrRecordType) qns
  forM_ qns $ \name -> do
    d <- ignoreAbstractMode (getConstInfo name)
    case theDef d of
      c@Constructor{} -> do
        (TelV args _) <- telView (defType d)
        allowed' <- forM args $ \ty -> do
          TelV _ ret <- telView (unDom ty)
          case unEl ret of
            Def name _ | name `Set.member` data_names -> pure (InductiveArg <$ ty)
            _ -> pure (NonInductiveArg <$ ty)
        let allowed = drop (conPars c) . fmap (snd . unDom) . telToList $ allowed'
        reportSDoc "tc.induction" 30 $
          "constructor name:" <+> prettyTCM name
            <+> "inductive args: " <+> prettyTCM (show allowed)
        modifySignature $ updateDefinition name $ updateTheDef $
          const c{ conInductiveArgs = Just allowed }
      _ -> pure ()
