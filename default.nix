# Nix file for Agda.
#
# To create a development environment, create a shell.nix file with this content:
#
# -----------------------------------
# with (import <nixpkgs> {}).pkgs;
# let
#   agda = pkgs.haskellPackages.callPackage ./. {};
# in agda.env
# -----------------------------------
#
# To enter the development environment, simply call `nix-shell shell.nix`.
#

{ mkDerivation, alex, array, base, binary, boxes, bytestring
, containers, cpphs, data-hash, deepseq, directory, edit-distance
, emacs, equivalence, filepath, geniplate-mirror, happy, hashable
, hashtables, haskeline, haskell-src-exts, mtl, parallel, pretty
, process, process-extras, QuickCheck, stdenv, strict, tasty
, regex-tdfa, regex-tdfa-text, filemanip
, tasty-silver, template-haskell, temporary, text, time
, transformers, transformers-compat, unordered-containers, xhtml
, murmur-hash, ieee754, gitrev
, zlib, tasty-quickcheck, monadplus, EdisonCore, EdisonAPI
, text-icu
, user-manual ? true, python34Packages, texlive, tex ? texlive.combine {
    inherit (texlive) scheme-full;
  }
, nodejs-6_x
# additional test dependencies
, wdiff, colordiff
}:

mkDerivation {
  pname = "Agda";
  version = "2.5.3";
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
  ];
  testDepends = [
    base containers directory filepath process-extras tasty
    regex-tdfa regex-tdfa-text
    tasty-silver temporary text
  ];
  configureFlags = [];
  buildTools = [ alex cpphs happy nodejs-6_x wdiff colordiff]
    ++ stdenv.lib.optionals user-manual [ python34Packages.sphinx python34Packages.sphinx_rtd_theme tex ];

  executableToolDepends = [ emacs ];

  postBuild = if user-manual then ''
    make doc-html
  '' else "";

  doCheck = false;

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
    mkdir -p $out/share/doc/Agda
    mv doc/user-manual/_build/html $out/share/doc/Agda/
  '';

  homepage = "http://wiki.portal.chalmers.se/agda/";
  description = "A dependently typed functional programming language and proof assistant";
  license = "unknown";
}
