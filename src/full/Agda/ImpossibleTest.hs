{-# LANGUAGE CPP #-}
module Agda.ImpossibleTest where

import Agda.Utils.Impossible

#include "undefined.h"

impossibleTest = __IMPOSSIBLE__
