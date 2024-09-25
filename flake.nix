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

      # The `agda` and `agda-mode` programs, built with `cabal build`
      # (and GHC & Haskell libraries from the nixpkgs snapshot)
      agda-pkg = hpkgs.developPackage {
          root = ./.;
          modifier = hlib.dontCheck;
          # TODO Make check phase work
          # At least requires:
          #   Setting AGDA_BIN (or using the Makefile, which at least requires cabal-install)
          #   Making agda-stdlib available (or disabling the relevant tests somehow)
        };

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
      packages.default = agda-pkg;        # Entry point for `nix build`
      devShells.default = agda-dev-shell; # Entry point for `nix develop`

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
