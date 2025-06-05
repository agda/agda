NOTE: Put drafts of release notes here that might be included in some
future release.

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


* Added support for [Cubical without Glue](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#cubical-agda-without-glue)
  by using the flag `--cubical-without-glue`,
  a variant of Cubical Agda which disables the Glue types.
  For compatibility with modules using `--cubical` and `--erased-cubical`, see
  [variants](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).
