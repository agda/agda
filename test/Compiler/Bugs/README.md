# Known compiler backend bugs

These tests record known exceptions when executing generated programs. Agda's
backend must compile the source successfully before the generated program is
run; the program must then terminate with a nonzero exit code. Compilation
failures and successful execution fail the test even with `--accept`.

Each test consists of an `.agda` (or literate Agda) source and an `.err` golden
containing normalized program output and runtime diagnostics. Optional
`.options` files select the affected backends and optimization modes using the
same `TestOptions` format as `../simple`. Optional `.inp` files provide standard
input. JavaScript verification during compilation is disabled, so exceptions
are tested during the explicit execution step.

This directory currently covers runtime exceptions, not successful execution
with incorrect output. Once a bug is fixed, move its test to `../simple` and
replace its `.err` golden with an `.out` golden for the correct execution.

Shared helpers belong in `../Include`, with module names such as `Include.Foo`.
Run these tests with `make AGDA_TESTS_OPTIONS='-j4 -p Bugs' compiler-test`.
