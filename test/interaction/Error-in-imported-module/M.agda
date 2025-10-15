module Error-in-imported-module.M where

open import Agda.Builtin.Nat

Foo : Nat
Foo = Nat

-- This module imports a non-primitive module to test the following
-- situation:
--
-- We're loading the client module (Error-in-imported-module.agda), and
-- in *that* TC state, which has not heard about Agda.Builtin.Nat, we
-- want to highlight the occurrences of Nat in the error message
-- generated here.
--
-- The Doc stores the DefinitionSite by TopLevelModuleName, so the
-- highlighting information needs to be lispified in a TC state that
-- *has* visited Agda.Builtin.Nat.
--
-- If we lispify the highlighting information for the error in the TC
-- state of the client module, then we get an __IMPOSSIBLE__. The
-- correct implementation uses the `ModuleToSource` that's bundled with
-- the error (if one exists, which, for a TC error, one does).
