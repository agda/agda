------------------------------------------------------------------------
-- A wrapper around incremental-parser
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor,
             MultiParamTypeClasses, FlexibleInstances #-}

module Incremental where

import Control.Applicative
import qualified Parser as Parser
import qualified Text.ParserCombinators.Incremental.Symmetric as Inc

newtype Parser k r' tok r = I { unI :: Inc.Parser [tok] r }
  deriving (Functor, Applicative, Alternative)

parse :: Parser k r' tok r -> [ tok ] -> [ r ]
parse p s =
  map fst $ filter (null . snd) $
    Inc.completeResults $ Inc.feedEof $ Inc.feed s (unI p)

instance Parser.Parser (Parser k r' tok) k r' tok where
  sym t = I $ do
    ts <- Inc.token [t]
    case ts of
      [t] -> return t
      _   -> empty
