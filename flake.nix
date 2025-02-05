{
  description = "Agda is a dependently typed programming language / interactive theorem prover.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
  inputs.flake-parts.url = "github:hercules-ci/flake-parts";

  outputs = inputs:
      inputs.flake-parts.lib.mkFlake { inputs = inputs; } {
    # Support all the OSes
    systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    perSystem = {pkgs, ...}: let
      hlib = pkgs.haskell.lib.compose;
      hpkgs = pkgs.haskellPackages;

      # Minimal nix code for building the `agda` executable.
      # GHC & Haskell libraries are taken from the nixpkgs snapshot.
      agda-pkg-minimal = hpkgs.developPackage {
          # N.B. this nix code never calls the `cabal` executable,
          # instead `hpkgs.developPackage` compiles Setup.hs with ghc
          # then runs ./Setup several times. This is implemented at
          # https://github.com/NixOS/nixpkgs/blob/a781ff33ae/pkgs/development/haskell-modules/generic-builder.nix
          root = ./.;
        };

      # Various builds of Agda

      # Recommended build
      agda-pkg = hlib.overrideCabal (_: {
          # These settings are documented at
          # https://ryantm.github.io/nixpkgs/languages-frameworks/haskell/#haskell-mkderivation

          # Don't run the test suite every build
          # (which is slow, and currently broken in nix)
          doCheck                   = false;

          # Disable optional outputs to speed up Agda's build
          enableLibraryProfiling    = false;  # Saved 221 seconds
          doHaddock                 = false;  # Saved  72 seconds
          doCoverage                = false;  # Saved   2 seconds
          enableExecutableProfiling = false;  # Saved   1 seconds
          enableStaticLibraries     = false;  # Saved  -1 seconds
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

      # Allow power users to set this flake's agda
      # as a drop-in replacement for nixpkgs's agda
      # (including as a dependency of other nixpkgs packages)
      # See https://flake.parts/overlays for more info
      overlayAttrs.packages.haskellPackages.agda = agda-pkg;
      # TODO: also replace each haskell.packages.ghcXXX.agda
    };
    # Generate the overlays.default output from overlayAttrs above
    # N.B. This overlay is EXPERIMENTAL and untested.
    # Please report bugs to the Agda issue tracker.
    imports = [ inputs.flake-parts.flakeModules.easyOverlay ];
  };
}
