# Nix file for Agda.
#
# To create a development environment, create a shell.nix file with this content:
#
# -----------------------------------
# with (import <nixpkgs> {}).pkgs;
# let
#   agda = pkgs.haskellPackages.callPackage ./. {};
# in agda.Agda.env
# -----------------------------------
#
# To enter the development environment, simply call `nix-shell shell.nix`.
#

{ mkDerivation, alex, array, base, binary, boxes, bytestring
, containers, cpphs, data-hash, deepseq, directory, edit-distance
, emacs, equivalence, filepath, geniplate-mirror, happy, hashable
, hashtables, haskeline, haskell-src-exts, mtl, parallel, pretty
, process, process-extras, QuickCheck, stdenv, strict, tasty
, regex-tdfa, regex-tdfa-text, filemanip, fail
, tasty-silver, tasty-hunit, template-haskell, temporary, text, time
, transformers, transformers-compat, unordered-containers, xhtml
, murmur-hash, ieee754, gitrev
, zlib, tasty-quickcheck, monadplus, EdisonCore, EdisonAPI
, text-icu
, ghc # we only need the explicit ghc for versions checks
, user-manual ? true, python34Packages, texlive, tex ? texlive.combine {
    inherit (texlive) scheme-full;
  }
, nodejs-6_x
# additional test dependencies
, wdiff, colordiff, bash, which, git, less, ghcWithPackages, inetutils
}:

let
  version = "2.5.3";
in rec {
  Agda = mkDerivation {
    pname = "Agda";
    version = version;
    src = ./.;
    isLibrary = true;
    isExecutable = true;
    buildDepends = [
      array base binary boxes bytestring containers data-hash deepseq
      directory edit-distance equivalence filepath geniplate-mirror
      hashable hashtables haskeline haskell-src-exts mtl parallel pretty
      process QuickCheck strict template-haskell text time transformers filemanip
      transformers-compat unordered-containers xhtml zlib tasty-quickcheck
      monadplus EdisonCore EdisonAPI murmur-hash ieee754 gitrev text-icu
    ] ++ (if stdenv.lib.versionOlder "8.0" ghc.version then [] else [ fail ]);
    testDepends = [
      base containers directory filepath process-extras tasty
      regex-tdfa regex-tdfa-text
      tasty-silver tasty-hunit temporary text
    ];
    configureFlags = [];
    buildTools = [ alex cpphs happy nodejs-6_x wdiff colordiff ]
      ++ stdenv.lib.optionals user-manual [ python34Packages.sphinx python34Packages.sphinx_rtd_theme tex ];

    executableToolDepends = [ emacs ];

    postBuild = if user-manual then ''
      pushd doc/user-manual
      make PDFLATEX=xelatex latexpdf
      make html
      popd
    '' else "";

    doCheck = false;
    doHaddock = false;

    postInstall = ''
      # Separate loops to avoid internal error
      files=($out/share/*-ghc-*/Agda-*/lib/prim/Agda/{Primitive.agda,Builtin/*.agda})
      for f in "''${files[@]}"
      do
        $out/bin/agda $f
      done
      for f in "''${files[@]}"
      do
        $out/bin/agda -c --no-main $f
      done
      $out/bin/agda-mode compile
      # copy user manual
      mkdir -p $out/share/doc/Agda/user-manual/
      cp -r doc/user-manual/_build/html $out/share/doc/Agda/user-manual/
      cp doc/user-manual/_build/latex/Agda.pdf $out/share/doc/Agda/user-manual/Agda-User-Manual.pdf

      mkdir -p $out/nix-support/
      echo "doc user-manual-html $out/share/doc/Agda/user-manual/html/" >> $out/nix-support/hydra-build-products
      echo "doc user-manual-pdf $out/share/doc/Agda/user-manual/Agda-User-Manual.pdf" >> $out/nix-support/hydra-build-products
    '';

    homepage = "http://wiki.portal.chalmers.se/agda/";
    description = "A dependently typed functional programming language and proof assistant";
    license = "unknown";
  };
  haddock = (Agda.override (orig: {
    pname = "Agda-haddock";
    doHaddock = true;
  })).overrideDerivation (orig: {
    dontBuild = true;
    installPhase = ''
      mkdir -p $out/share/doc/Agda/haddock
      cp -r dist/doc/html/Agda/* $out/share/doc/Agda/haddock/

      mkdir -p $out/nix-support/
      echo "doc agda-haddock $out/share/doc/Agda/haddock/" >> $out/nix-support/hydra-build-products
    '';
  });

  tests = {
    api = stdenv.mkDerivation {
      name = "tests-api";
      src = ./.;
      buildInputs = [ bash which (ghcWithPackages (h: [ Agda ])) ];
      dontBuild = true;
      doCheck = true;
      checkPhase = ''
        make AGDA_BIN=${Agda}/bin/agda AGDA_TESTS_BIN=$PWD/test/dist/build/agda-tests/agda-tests AGDA_TESTS_OPTIONS=""\
          api-test
      '';
      installPhase = ''
        mkdir -p $out
      '';
    };
    # TODO BROKEN: The agda tests are using --ignore-interfaces, but with this flag Agda tries to recompile
    # Primitive.agda and we don't have write permissions for that file.
    benchmark = stdenv.mkDerivation {
      name = "tests-benchmark";
      src = ./.;
      buildInputs = [ bash which ghc inetutils ];
      dontBuild = true;
      doCheck = true;
      checkPhase = ''
        make AGDA_BIN=${Agda}/bin/agda AGDA_TESTS_BIN=$PWD/test/dist/build/agda-tests/agda-tests AGDA_TESTS_OPTIONS=""\
          benchmark-without-logs
      '';
      installPhase = ''
        mkdir -p $out
      '';
    };

  };
}
