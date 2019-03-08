{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans ( lift )

import Data.Either (lefts)
import qualified Data.List as List
import Data.Monoid (Any(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Position
-- import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

-- import Agda.TypeChecking.Rules.LHS (checkSortOfSplitVar)
-- import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
-- import Agda.TypeChecking.Rules.LHS.Unify

-- import Agda.TypeChecking.Coverage.Match
-- import Agda.TypeChecking.Coverage.SplitTree

import Agda.TypeChecking.Conversion (tryConversion, equalType, equalTermOnFace)
-- import Agda.TypeChecking.Datatypes (getConForm)
-- import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyTel)
-- import Agda.TypeChecking.Free
-- import Agda.TypeChecking.Irrelevance
-- import Agda.TypeChecking.Patterns.Internal (dotPatternsToPatterns)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
-- import Agda.TypeChecking.MetaVars
-- import Agda.TypeChecking.Warnings

-- import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

checkIApplyConfluence_ :: QName -> TCM ()
checkIApplyConfluence_ f = do
  reportSDoc "tc.cover.iapply" 10 $ text "Checking IApply confluence of" <+> pretty f
  inConcreteOrAbstractMode f $ \ d -> do
  case theDef d of
    Function{funClauses = cls', funCovering = cls} -> do
      reportSDoc "tc.cover.iapply" 10 $ text "length cls =" <+> pretty (length cls)
      when (null cls && not (null $ concatMap (iApplyVars . namedClausePats) cls')) $
        __IMPOSSIBLE__
      modifySignature $ updateDefinition f $ updateTheDef
        $ updateCovering (const [])

      forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | @addClause f (Clause {namedClausePats = ps})@ checks that @f ps@
-- reduces in a way that agrees with @IApply@ reductions.
checkIApplyConfluence :: QName -> Closure Clause -> TCM ()
checkIApplyConfluence f clos = do
  enterClosure clos $ \ cl ->
    case cl of
      Clause {clauseBody = Nothing} -> return ()
      Clause {clauseType = Nothing} -> __IMPOSSIBLE__
      cl@Clause { clauseTel = tel
                , namedClausePats = ps
                , clauseType = Just t
                , clauseBody = Just body
                } -> setCurrentRange (clauseLHSRange cl) $ do
          let
            trhs = unArg t
          ps <- normaliseProjP ps
          forM_ (iApplyVars ps) $ \ i -> do
            unview <- intervalUnview'
            let phi = unview $ IMax (argN $ var $ i) $ argN $ unview (INeg $ argN $ var i)
            let es = patternsToElims ps
            let lhs = Def f es
            equalTermOnFace phi trhs lhs body

