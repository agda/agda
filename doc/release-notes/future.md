NOTE: Put drafts of release notes here that might be included in some
future release.

Paths
-----

* Agda no longer "canonicalises" all paths
  ([#6146](https://github.com/agda/agda/issues/6146)).

  This means, for instance, that one can save the module `A.B` in
  the file `C/D/B.agda` if there is a symbolic link from `A` to `C/D`.
  However, this only works if Agda is given the path `A/B.agda`, not
  if the path `C/D/B.agda` is used:
  ```
  $ mkdir -p C/D
  $ ln -s C/D A
  $ echo 'module A.B where' > A/B.agda
  $ agda A/B.agda
  Checking A.B (A/B.agda).
  $ agda C/D/B.agda
  The module A.B should be in the directory A/B, but Agda was given
  the path C/D/B.agda.
  ```
  Note also that Agda no longer accepts use of `..` in the
  "hierarchical module name part" of the file name:
  ```
  $ mkdir -p E/F
  $ echo 'module E.F where' > E/F.agda
  $ agda E/F/../F.agda
  The module E.F should be in the directory E/F, but Agda was given
  the path E/F/../F.agda.
  ```
  However, use of `..` is accepted before the hierarchical module name
  part:
  ```
  $ mkdir -p G/H
  $ echo 'module H where' > G/H.agda
  $ agda -iG G/../G/H.agda
  Checking H (G/../G/H.agda).
  ```

Library management
------------------

* A different method is now used to search for `.agda-lib` files
  ([#5673](https://github.com/agda/agda/issues/5673)).

  Consider the module `A.B.C` in the directory `dir/A/B`. Previously
  Agda searched for possible `.agda-lib` files for this module in the
  following way:
  1. Make the path `dir` "canonical" using
     [`canonicalizePath`](https://hackage.haskell.org/package/directory-1.3.8.0/docs/System-Directory.html#v:canonicalizePath).
     Denote the resulting path by `cdir`.
  2. Search for `.agda-lib` files in `cdir`.
  3. If no `.agda-lib` files were found: Denote the canonical variant
     of the parent of `cdir` by `parent`. If `cdir` is equal to
     `parent`, stop. Otherwise continue the search (from step 2) in
     `parent`.

  Now the following procedure is used instead:
  1. Turn the directory `dir` into an absolute path (by prepending the
     current working directory, if necessary).
  2. If the resulting path is `/a/b/c`, say, then the directories
     `/a/b/c`, `/a/b`, `/a` and `/` are searched, in that order.

  This can make a difference in the presence of symbolic links.

Pragmas and Options
-------------------

* The option `--termination-depth` is now obsolete.

  The default termination depth is now infinity instead of
  (previously) 1.  This means that setting `--termination-depth` might
  now make the termination checker *weaker* (instead of stronger).
  However, there is no guaranteed effect of setting
  `--termination-depth` any more.  The flag is only kept for debugging
  Agda.

  For example, the following code now passes the termination checker
  (needed higher `--termination-depth` before):

  ```agda
  f : Nat → Nat
  g : Nat → Nat

  f zero                = zero
  f (suc zero)          = zero
  f (suc (suc zero))    = zero
  f (suc (suc (suc n))) = g n     -- decrease by 3

  g n = f (suc (suc n))           -- increase by 2
  ```

  [See also Issue [#709](https://github.com/agda/agda/issues/709)]
