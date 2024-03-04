# Test Migration Progress

## Tests from tasty `Main.hs`

| Status | Fail | Total | Old name in `Main.hs` |         How to run now          |
| ------ | ---: | ----: | --------------------- | ------------------------------- |
| 🛠️     |    4 |  1784 | SUCCEED.tests         | `cabal run test-succeed`        |
| 🛠️     |   10 |  1552 | FAIL.tests            | `cabal run test-fail`           |
| 🛠️     |    1 |    15 | BUGS.tests            | `cabal run test-bugs`           |
| ✅      |    0 |     3 | INTERACTIVE.tests     | `cabal run test-interactive`    |
| ✅      |    0 |    52 | USERMANUAL.tests      | `cabal run test-usermanual`     |
| ✅      |    0 |    87 | LATEXHTML.tests       | `cabal run test-latexhtml`      |
| ✅      |    0 |   505 | INTERNAL.tests        | `cabal run test-internal`       |
| 🛠️     |   24 |   354 | COMPILER.tests        | `cabal run test-compiler`       |
| ✅      |    0 |    25 | LIBSUCCEED.tests      | `cabal run test-libsucceed`     |
| ✅      |    0 |     1 | CUBICALSUCCEED.tests  | `cabal run test-cubicalsucceed` |

## Tests from the [`test : ` target of the `Makefile`]

| Status |  Old name in `Makefile` |  How to run now |
| ------ | ---------------------- |  ----------------------------- |
| ✅ | check-whitespace       | `cabal run check-whitespace` |
| ✅ | check-encoding         | `cabal run Emojicheck-encoding`   |
| ❌ | common                 |                              |
| 🫛 | succeed                | `cabal run test-succeed`     |
| 🫛 | fail                   | `cabal run test-fail`        |
| 🫛 | bugs                   | `cabal run test-bugs`        |
| 🫛 | interaction            | `cabal run test-interaction` |
| ❌ | examples               |                              |
| ❌ | std-lib-test           |                              |
| ❌ | cubical-test           |                              |
| ❌ | interactive            |                              |
| ❌ | latex-html-test        |                              |
| ❌ | api-test               |                              |
| 🫛 | internal-tests         | `cabal run test-internal`    |
| ❌ | benchmark-without-logs |                              |
| 🫛 | compiler-test          | `cabal run test-compiler`    |
| ❌ | std-lib-compiler-test  |                              |
| 🫛 | std-lib-succeed        | `cabal run test-libsucceed`  |
| 🫛 | std-lib-interaction    | `cabal run test-interaction` |
| 🫛 | user-manual-test       | `cabal run test-usermanual`  |
| ❌ | doc-test               |                              |
| ❌ | size-solver-test       |                              |

## Tidy-up

| Status |                   Task                    |
| ------ | ----------------------------------------- |
| ✅      | Update tasty `Main.hs`                    |
| ❌      | Update `Makefile`                         |
| ❌      | Update CI                                 |
| ❌      | Update `HACKING.md`                       |
| ❌      | Look for test duplication by `cabal test` |
| ❌      | Minimize diff vs. `master`                |
| ❌      | Delete this file, squash, merge           |

## Legend

| Emoji |  Meaning  |
| ----- | --------- |
| ❌     | not done  |
| 🛠️    | WIP/buggy |
| ✅     | done      |
| 🫛     | duplicate |

[`test : ` target of the `Makefile`]: Makefile#L444
