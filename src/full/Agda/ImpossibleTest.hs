{-# OPTIONS_GHC -fwarn-missing-signatures #-}

{-# LANGUAGE CPP #-}

module Agda.ImpossibleTest where

#include "undefined.h"
import Agda.Utils.Impossible

impossibleTest :: a
impossibleTest = __IMPOSSIBLE__
