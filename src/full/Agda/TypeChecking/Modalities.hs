{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Modalities
  ( checkModality'
  , checkModality
  , checkModalityArgs
  ) where

import Control.Applicative ((<|>))

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkRelevance' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkRelevance' x def = do
  case getRelevance def of
    Relevant{} -> return Nothing -- relevance functions can be used in any context.
    drel -> do
      -- Andreas,, 2018-06-09, issue #2170
      -- irrelevant projections are only allowed if --irrelevant-projections
      let isProj = theDef def ^. funProj
      ifM (pure isProj `and2M`
           (not . optIrrelevantProjections <$> pragmaOptions)) {-then-} needIrrProj {-else-} $ do
        rel <- viewTC eRelevance
        reportSDoc "tc.irr" 50 $ vcat
          [ "declaration relevance =" <+> text (show drel)
          , "context     relevance =" <+> text (show rel)
          , prettyTCM x <+> "is" <+> applyUnless isProj ("not" <+>) "a projection"
          ]
        return $ boolToMaybe (not $ drel `moreRelevant` rel) $ DefinitionIsIrrelevant x
  where
  needIrrProj = return $ Just $ ProjectionIsIrrelevant x

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkQuantity' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkQuantity' x def = do
  case getQuantity def of
    dq@Quantityω{} -> do
      reportSDoc "tc.irr" 50 $ vcat
        [ "declaration quantity =" <+> text (show dq)
        -- , "context     quantity =" <+> text (show q)
        ]
      return Nothing -- Abundant definitions can be used in any context.
    dq -> do
      q <- viewTC eQuantity
      reportSDoc "tc.irr" 50 $ vcat
        [ "declaration quantity =" <+> text (show dq)
        , "context     quantity =" <+> text (show q)
        ]
      return $ boolToMaybe (not $ dq `moreQuantity` q) $ DefinitionIsErased x

-- | The second argument is the definition of the first.
checkModality' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkModality' x def = do
  relOk <- checkRelevance' x def
  qtyOk <- checkQuantity' x def
  return $ relOk <|> qtyOk

-- | The second argument is the definition of the first.
checkModality :: (MonadConversion m) => QName -> Definition -> m ()
checkModality x def = checkModality' x def >>= mapM_ typeError

-- | Checks that the given implicitely inserted arguments, are used in a modally
--   correct way.
checkModalityArgs :: (MonadConversion m) => Definition -> Args -> m ()
checkModalityArgs d vs = do
  let
    vmap :: VarMap
    vmap = freeVars vs

  -- we iterate over all vars in the context and their ArgInfo,
  -- checking for each that "vs" uses them as allowed.
  as <- getContextArgs
  forM_ as $ \ (Arg avail t) -> do
    let m = do
          v <- deBruijnView t
          varModality <$> lookupVarMap v vmap
    whenJust m $ \ used -> do
      let availPosMod = positionalModalityComponent (getModality avail)
          usedPosMod = positionalModalityComponent (getModality used)
      unless (availPosMod `moreUsableModality` usedPosMod) $
         typeError $ InvalidModalTelescopeUse t usedPosMod availPosMod d
