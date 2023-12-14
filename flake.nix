{
  description = "Agda is a dependently typed programming language / interactive theorem prover.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    # Support all the OSes
    (flake-utils.lib.eachDefaultSystem (system: let

    pkgs = nixpkgs.legacyPackages.${system};
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
          hpkgs.fix-whitespace
          # Tools for building the agda docs
          (pkgs.python3.withPackages (py3pkgs: [
            py3pkgs.sphinx
            py3pkgs.sphinx_rtd_theme
          ]))
        ];

      # Include an offline-usable `hoogle` command
      # pre-loaded with all the haskell dependencies
      withHoogle = true;
    };

  in {
    packages.default = agda-pkg;        # Entry point for `nix build`
    devShells.default = agda-dev-shell; # Entry point for `nix develop`
  }));
}
