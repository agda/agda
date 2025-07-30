{
  description = "Agda is a dependently typed programming language / interactive theorem prover.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
  inputs.flake-parts.url = "github:hercules-ci/flake-parts";

  outputs = inputs:
      inputs.flake-parts.lib.mkFlake { inputs = inputs; } {
    # Support all the OSes
    systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    perSystem = {pkgs, ...}: let
      hlib = pkgs.haskell.lib.compose;
      hpkgs = pkgs.haskell.packages.ghc910; # pqueue fails with ghc 912
      fs = pkgs.lib.fileset;

      # Minimal nix code for building the `agda` executable.
      # GHC & Haskell libraries are taken from the nixpkgs snapshot.
      agda-pkg-minimal = hpkgs.developPackage {
          # N.B. this nix code never calls the `cabal` executable,
          # instead `hpkgs.developPackage` compiles Setup.hs with ghc
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

      # Recommended build
      agda-pkg = hlib.overrideCabal (drv: {
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
        }) agda-pkg-minimal;

      # An even faster Agda build, achieved by asking GHC to optimize less
      agda-pkg-quicker =
        # `appendConfigureFlag` passes a raw argument to ./Setup
        hlib.appendConfigureFlag "-O0" agda-pkg;

      # No-output Agda build (type check only)
      agda-pkg-tc =
        hlib.appendConfigureFlags ["--ghc-option" "-fno-code"] agda-pkg-quicker;

      # Agda supporting the `-v` option
      agda-pkg-debug = hlib.enableCabalFlag "debug" agda-pkg;

      # Development environment with tools for hacking on agda
      agda-dev-shell = hpkgs.shellFor {
        # Which haskell packages to prepare a dev env for
        packages = _: [agda-pkg];
        # Extra software to provide in the dev shell
        nativeBuildInputs = [
            # Tools for building agda
            pkgs.cabal-install
            pkgs.haskell-language-server
            pkgs.icu
            hpkgs.fix-whitespace
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

    in {
      packages.default    = agda-pkg;        # Entry point for `nix build`
      packages.quicker    = agda-pkg-quicker;# Entry point for `nix build .#quicker`
      packages.debug      = agda-pkg-debug;  # Entry point for `nix build .#debug`
      packages.type-check = agda-pkg-tc;     # Entry point for `nix build .#type-check`
      devShells.default   = agda-dev-shell;  # Entry point for `nix develop`

      # Allow users to set this flake's agda as a drop-in replacement for nixpkgs's agda
      # (including as a dependency of other nixpkgs packages)
      # See https://flake.parts/overlays for more info
      overlayAttrs.haskell = pkgs.haskell // {
        packageOverrides = pkgs.lib.composeExtensions pkgs.haskell.packageOverrides
          (hfinal: hprev: {
            Agda = agda-pkg;
          });
      };
    };

    imports = [ inputs.flake-parts.flakeModules.easyOverlay ];
  };
}
