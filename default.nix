{ mkDerivation, alex, array, base, binary, boxes, bytestring
, containers, cpphs, data-hash, deepseq, directory, edit-distance
, emacs, equivalence, filepath, geniplate-mirror, happy, hashable
, hashtables, haskeline, haskell-src-exts, mtl, parallel, pretty
, process, process-extras, QuickCheck, stdenv, strict, tasty
, regex-tdfa, regex-tdfa-text, filemanip
, tasty-silver, template-haskell, temporary, text, time
, transformers, transformers-compat, unordered-containers, xhtml
, zlib, tasty-quickcheck, sphinx, sphinx_rtd_theme
, uhc-backend ? false, uhc ? null, uhc-light ? null
}:

assert uhc-backend -> uhc != null && uhc-light != null;

mkDerivation {
  pname = "Agda";
  version = "2.4.3";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  buildDepends = [
    array base binary boxes bytestring containers data-hash deepseq
    directory edit-distance equivalence filepath geniplate-mirror
    hashable hashtables haskeline haskell-src-exts mtl parallel pretty
    process QuickCheck strict template-haskell text time transformers filemanip
    transformers-compat unordered-containers xhtml zlib uhc-light tasty-quickcheck
  ];
  testDepends = [
    base containers directory filepath process-extras tasty
    regex-tdfa regex-tdfa-text
    tasty-silver temporary text
  ];
  configureFlags = if uhc-backend then [ "-fuhc" ] else [];
  buildTools = [ alex cpphs emacs happy uhc sphinx sphinx_rtd_theme ];
  postInstall = ''
    $out/bin/agda -c --no-main $(find $out/share -name Primitive.agda)
    $out/bin/agda-mode compile
  '';
  homepage = "http://wiki.portal.chalmers.se/agda/";
  description = "A dependently typed functional programming language and proof assistant";
  license = "unknown";
}
