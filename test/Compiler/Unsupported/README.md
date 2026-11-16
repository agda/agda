# Unsupported compilation

These tests type-check, but Agda's GHC or JavaScript backend must reject their
compilation, for example because full Cubical Agda is unsupported. They test
Agda's own diagnostics, rather than rejection of generated Haskell by GHC or
exceptions when executing generated JavaScript.

Each test consists of an `.agda` (or literate Agda) source and an `.err` golden
containing Agda's diagnostic. An optional `.options` file uses the same
`TestOptions` format as `../simple`: `forCompilers` selects backends and modes,
and `extraAgdaArgs` supplies additional options for each backend.

The runner first checks the source without a backend. It then invokes the
selected backend without calling GHC or verifying generated JavaScript. The
backend must fail with an ordinary Agda error (exit code 42), rather than an
external compilation error or an internal error. Successful compilation and
front-end errors fail the test even with `--accept`.

Shared helper modules belong in `../Include`, with module names such as
`Include.Foo`. They are imported by tests, not discovered as independent tests.

Run these tests with `make AGDA_TESTS_OPTIONS='-j4 -p Unsupported' compiler-test`.
