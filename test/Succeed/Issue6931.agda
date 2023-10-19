-- Andreas, Oskar, issue #6931:
-- Dead code analysis should not prune telescopes of empty modules.

module _ where

postulate A : Set

open import Issue6931.One A
import Issue6931.Three as Three

module M = Three.Public A b
module N = Three.HasPrivate A b
