# Succeed tests

Put compiler backend options in the test's `.flags` file,
rather than an `OPTIONS` pragma in its Agda source. For example, options for
`Example.agda` belong in `Example.flags`. The runner splits the file into
whitespace-separated arguments.

When `AGDA_NO_EXEC` is set, the test runner scans `.flags` files to discover
tests that may launch external processes and skips them. It does this before
running Agda, so options hidden in source pragmas would escape discovery.
The scan includes nested directories and applies to literate Agda tests too.

The scan discovers tests that enable the GHC backend with `--ghc`,
`--compile`, or `-c`. GHC tests using `--ghc-dont-call-ghc` remain enabled
because they only generate code. JavaScript backend options alone do not cause a
test to be skipped: generating JavaScript does not launch an external compiler.

Keep compiler backend options in `.flags` when adding or changing tests so
the compiler filter stays up to date automatically.

Tests using `--allow-exec` are an exception: keep that option in an `OPTIONS`
pragma and add the test to the manual `allowExecTests` list in `execTestFilter`
in `Tests.hs`. Passing `--allow-exec` on the command line also enables it for
imported builtin modules, whose `--safe` pragmas are incompatible with it.
The manual list lets `AGDA_NO_EXEC` skip these tests without moving the option
to the command line.
