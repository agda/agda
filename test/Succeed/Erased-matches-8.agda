-- A module that uses --erased-matches=none can import a module that
-- does not use --erasure.

{-# OPTIONS --erased-matches=none #-}

module Erased-matches-8 where

import Erased-matches.No-erasure
