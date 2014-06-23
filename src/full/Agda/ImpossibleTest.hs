{-# LANGUAGE CPP #-}

module Agda.ImpossibleTest where

#include "undefined.h"
import Agda.Utils.Impossible

impossibleTest = __IMPOSSIBLE__
