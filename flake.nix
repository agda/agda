{
  description = "Agda is a dependently typed programming language / interactive theorem prover.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
  inputs.flake-parts.url = "github:hercules-ci/flake-parts";
  inputs.ghc-wasm.url = "git+https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta.git";

  outputs = inputs:
      inputs.flake-parts.lib.mkFlake { inputs = inputs; } {
    # Support all the OSes
    systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    perSystem = { system, pkgs, inputs', ... }: let
      hlib = pkgs.haskell.lib.compose;
      hpkgs = pkgs.haskell.packages.ghc910; # pqueue fails with ghc912
      fs = pkgs.lib.fileset;
      ghc-wasm = inputs'.ghc-wasm;

      # An overlay for the Haskell package set that adds various builds of Agda
      # and replaces `Agda` with a default one.
      agdaOverrides = hpkgs: hprev: {
        # Minimal nix code for building the `agda` executable.
        # GHC & Haskell libraries are taken from the nixpkgs snapshot.
        Agda-minimal = hpkgs.developPackage {
          # N.B. this nix code never calls the `cabal` executable,
          # instead `developPackage` compiles Setup.hs with ghc
          # then runs ./Setup several times. This is implemented at
          # https://github.com/NixOS/nixpkgs/blob/a781ff33ae/pkgs/development/haskell-modules/generic-builder.nix

          # A minimal set of files to copy into nix's build sandbox.
          # Whenever these files change, `nix build` recompiles Agda.
          root = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./src/setup
              ./src/full
              ./src/main
              ./src/data
              ./src/agda-mode
              ./Agda.cabal
              ./LICENSE
              (fs.difference  # agda-tests Haskell source
                (fs.fileFilter (file: file.hasExt "hs") ./test)
                ./test/interaction  # Haskell files not for agda-tests
              )
            ];
          };

          modifier = hlib.overrideCabal (drv: {
            # Typecheck the primitive modules.
            postInstall = drv.postInstall or "" + ''
              agdaExe=''${bin:-$out}/bin/agda

              echo "Generating Agda core library interface files..."
              (cd "$("$agdaExe" --print-agda-data-dir)/lib/prim" && "$agdaExe" --build-library)
            '';
          });
        };

        # Various builds of Agda

        # Basic build (no debugging information)
        Agda-base = hlib.overrideCabal (drv: {
          # These settings are documented at
          # https://nixos.org/manual/nixpkgs/unstable/#haskell-mkderivation

          # Don't run the test suite every build
          # (which is slow, and currently broken in nix)
          doCheck                   = false;

          # Disable optional outputs to speed up Agda's build
          enableLibraryProfiling    = false;  # Saved 221 seconds
          doHaddock                 = false;  # Saved  72 seconds
          doCoverage                = false;  # Saved   2 seconds
          enableExecutableProfiling = false;  # Saved   1 seconds
          enableStaticLibraries     = false;  # Saved  -1 seconds

          # Place the binaries in a separate output with a much smaller closure size.
          enableSeparateBinOutput = true;
          mainProgram = "agda";
        } // pkgs.lib.optionalAttrs (pkgs.stdenv.hostPlatform.isDarwin && pkgs.stdenv.hostPlatform.isAarch64) {
          # A nixpkgs-specific patch for aarch64-darwin related to the separate bin output
          # causes a warning about some functions being removed from Paths_Agda, which
          # we can just ignore. See https://github.com/agda/agda/issues/8016
          configureFlags = drv.configureFlags or [] ++ [
            "--ghc-option=-Wwarn=deprecations"
          ];
        }) hpkgs.Agda-minimal;

        # An even faster Agda build, achieved by asking GHC to optimize less
        Agda-quicker =
          # `appendConfigureFlag` passes a raw argument to ./Setup
          hlib.appendConfigureFlag "-O0" hpkgs.Agda-base;

        # No-output Agda build (type check only)
        Agda-tc =
          hlib.appendConfigureFlags ["--ghc-option" "-fno-code"] hpkgs.Agda-quicker;

        # Agda supporting the `-v` option
        Agda-debug = hlib.enableCabalFlag "debug" hpkgs.Agda-base;

        # Use a debug-enabled build by default.
        Agda = hpkgs.Agda-debug;

        # Development environment with tools for hacking on agda
        Agda-dev-shell = hpkgs.shellFor {
          # Which haskell packages to prepare a dev env for
          packages = h: [h.Agda];
          # Extra software to provide in the dev shell
          nativeBuildInputs = [
              # Tools for building agda
              pkgs.cabal-install
              pkgs.haskell-language-server
              pkgs.icu
              hpkgs.fix-whitespace

              # Tools for building/testing WASM
              ghc-wasm.packages.wasm32-wasi-ghc-9_10
              ghc-wasm.packages.wasm32-wasi-cabal-9_10
              ghc-wasm.packages.wasmtime

              # Tools for building the agda docs
              (pkgs.python3.withPackages (py3pkgs: [
                py3pkgs.sphinx
                py3pkgs.sphinx_rtd_theme
              ]))
              # Tools for running the agda test-suite
              pkgs.nodejs_22
            ];

          # Include an offline-usable `hoogle` command
          # pre-loaded with all the haskell dependencies
          withHoogle = true;
        };
      };

      # Makefile targets to run
      test-suites =
        [

          # Makefile targets run by `make test`:
            "check-whitespace"
            "check-encoding"
            "check-mdo"
            "common"
            "succeed"
            "fail"
            "bugs"
            # "interaction"     # runs Haskell scripts that import Agda
            "examples"
            # "std-lib-test"    # requires std-lib submodule, runs its cabal build
            # "cubical-test"    # requires cubical submodule, runs its cabal build
            "interactive"
            # "latex-html-test" # requires agda built with `-fenable-cluster-counting`, which breaks `nix build`
            # "api-test"        # runs Haskell scripts that import Agda
            "internal-tests"
            # "benchmark-without-logs"  # requires std-lib submodule
            "compiler-test"
            # "std-lib-compiler-test" # requires running std-lib-test first
            # "std-lib-succeed"       # requires running std-lib-test first
            # "std-lib-interaction"   # requires running std-lib-test first
            # "doc-test"  # runs cabal with custom compiler
            "user-manual-test"
            # "size-solver-test"  # Makefile recipe commented out

          # Other Makefile targets run by CI
            "user-manual-covers-options"
            "user-manual-covers-warnings"
            "test-suite-covers-warnings"
            "test-suite-covers-errors"
        ];

      # Runs `make ${target}`
      # To run more fine-grained tests:
      #   1. Enter the sandbox with e.g. `nix develop .#succeed`
      #   2. Run testing commands, e.g.
      #     * `make succeed`
      #     * `agda-tests -p 641`
      test-results-for = target: pkgs.stdenv.mkDerivation {
        name = "${target}.txt";
        src = ./.;  # Some tests scan all files in the repo work tree
        buildInputs =
        [
          pkgs.which            # For Makefile
          hpkgs.fix-whitespace  # For Makefile's `check-whitespace` target
          hpkgs.ghc             # For agda-tests's Compiler.Tests
          pkgs.nodejs_22        # For agda-tests's Compiler.Tests
          hpkgs.Agda            # For manual testing with `agda` and `agda-tests`
        ];
        AGDA_BIN = "${pkgs.lib.getBin hpkgs.Agda}/bin/agda";
        AGDA_TESTS_BIN = "${pkgs.lib.getBin hpkgs.Agda}/bin/agda-tests";
        LC_ALL = "C.UTF-8"; # Support Unicode
        buildPhase = ''
          set -euo pipefail
          make ${target} | tee $name
        '';
        installPhase = ''
          mkdir $out
          cp $name $out
        '';
      };

      # Builds a directory of test logs, one per test-suite
      all-test-results = pkgs.symlinkJoin {
        name = "agda-test-results";
        paths = pkgs.lib.map test-results-for test-suites;
      };

    in {
      # Apply our overlay to the `pkgs` argument.
      _module.args.pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [
          (final: prev: {
            haskell = prev.haskell // {
              packageOverrides = pkgs.lib.composeExtensions prev.haskell.packageOverrides agdaOverrides;
            };
          })
        ];
      };

      packages = {
        default    = hpkgs.Agda;         # Entry point for `nix build`
        base       = hpkgs.Agda-base;    # Entry point for `nix build .#base`
        quicker    = hpkgs.Agda-quicker; # Entry point for `nix build .#quicker`
        debug      = hpkgs.Agda-debug;   # Entry point for `nix build .#debug`
        type-check = hpkgs.Agda-tc;      # Entry point for `nix build .#type-check`
        test       = all-test-results;   # Entry point for `nix build .#test`
      } // pkgs.lib.listToAttrs (pkgs.lib.forEach test-suites (target: {
        name = target; # Entry point for e.g. `nix build .#compiler-test`
        value = test-results-for target;
      }));
      devShells.default = hpkgs.Agda-dev-shell;  # Entry point for `nix develop`

      # Allow users to set this flake's Agda as a drop-in replacement for nixpkgs's Agda
      # (including as a dependency of other nixpkgs packages)
      # See https://flake.parts/overlays for more info
      overlayAttrs.haskell = pkgs.haskell // {
        packageOverrides = pkgs.lib.composeExtensions pkgs.haskell.packageOverrides agdaOverrides;
      };
    };

    imports = [ inputs.flake-parts.flakeModules.easyOverlay ];
  };
}
