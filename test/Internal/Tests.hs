-- | Responsible for grouping all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Internal.Tests ( tests ) where

import Internal.Helpers

import qualified Internal.Compiler.MAlonzo.Encode                  as CompEnco     ( tests )
import qualified Internal.Interaction.Highlighting.Precise         as IntePrec     ( tests )
import qualified Internal.Interaction.Highlighting.Range           as InteRang     ( tests )
import qualified Internal.Interaction.Library                      as Library      ( tests )
import qualified Internal.Interaction.Options                      as InteOpti     ( tests )
import qualified Internal.Syntax.Common                            as SyntCommon   ( tests )
import qualified Internal.Syntax.Internal                          as SyntInternal ( tests )
import qualified Internal.Syntax.Parser.Parser                     as SyntPars     ( tests )
import qualified Internal.Syntax.Position                          as SyntPosi     ( tests )
import qualified Internal.Termination.CallGraph                    as TermCall     ( tests )
import qualified Internal.Termination.CallMatrix                   as TermCM       ( tests )
import qualified Internal.Termination.Order                        as TermOrd      ( tests )
import qualified Internal.Termination.Semiring                     as TermRing     ( tests )
import qualified Internal.Termination.SparseMatrix                 as TermSparse   ( tests )
import qualified Internal.Termination.Termination                  as TermTerm     ( tests )
import qualified Internal.TypeChecking                             as TypeChck     ( tests )
import qualified Internal.TypeChecking.Free                        as Free         ( tests )
import qualified Internal.TypeChecking.Generators                  as Generators   ( tests )
import qualified Internal.TypeChecking.Irrelevance                 as Irrel        ( tests )
import qualified Internal.TypeChecking.Monad.Base                  as MBase        ( tests )
import qualified Internal.TypeChecking.Positivity                  as Positivity   ( tests )
import qualified Internal.TypeChecking.Positivity.Occurrence       as Occurrence   ( tests )
import qualified Internal.TypeChecking.Rules.LHS.Problem           as LHSProblem   ( tests )
import qualified Internal.TypeChecking.SizedTypes                  as SizedTypes   ( tests )
import qualified Internal.TypeChecking.Substitute                  as Substitute   ( tests )

-- Keep this list in the import order, please!
tests :: TestTree
tests = testGroup "Internal"
  [ CompEnco.tests
  , IntePrec.tests
  , InteRang.tests
  , Library.tests
  , InteOpti.tests
  , SyntCommon.tests
  , SyntInternal.tests
  , SyntPars.tests
  , SyntPosi.tests
  , TermCall.tests
  , TermCM.tests
  , TermOrd.tests
  , TermRing.tests
  , TermSparse.tests
  , TermTerm.tests
  , TypeChck.tests
  , Free.tests
  , Generators.tests
  , Irrel.tests
  , MBase.tests
  , Positivity.tests
  , Occurrence.tests
  , LHSProblem.tests
  , SizedTypes.tests
  , Substitute.tests
  ]
