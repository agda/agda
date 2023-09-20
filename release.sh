#!/bin/bash

set -ue
PATH=./.cabal-sandbox/bin${PATH:+:$PATH}

ChoicesQuestion() {
    local question="$1" default="$2" first="$3" ans
    shift; shift; shift
    while true; do
        {   echo -n "$question ["
            [ "$default" = "$first" ] && echo -n "$first" | tr '[:lower:]' '[:upper:]' || echo -n "$first"
            for c in "$@"; do
                echo -n '/'
                [ "$default" = "$c" ] && echo -n "$c" | tr '[:lower:]' '[:upper:]' || echo -n "$c"
            done
            echo -n '] '
            read -r ans;
        } </dev/tty >/dev/tty
        if ! [ "$ans" ]; then
            echo "$default"
            return
        else
            for c in "$first" "$@"; do
                [ "$ans" != "$c" ] || { echo "$ans"; return; }
            done
        fi
    done
}
YesNoQuestion() {
    local r=$(ChoicesQuestion "$1" "${2:-y}" y n)
    [ "$r" = y ]
}

Question() {
    local question="$1" default="$2" ans
    echo -n "$question [$default] " >/dev/tty
    read -r ans </dev/tty
    [ "$ans" ] || ans="$default"
    echo "$ans"
}

edit() {
    [ "${EDITOR:-}" ] || { echo "$$EDITOR is not set." >&2; exit 1; }
    $EDITOR "$1"
    [ ! -s "$1" ] || git add -v "$1"
}

updateVersion() {
    local version="$1"

    # Update the version number in the cabal file
    sed -ri "s/^(version:\s+).*/\1$version/
             s/\b(Agda\s+==\s+)[0-9.]+(,?)/\1$version\2/" \
        Agda.cabal

    # Update the version number in the elisp file
    sed -ri "s/(\(\s*defvar\s+agda2-version\s+)\"[0-9.]+\"/\1\"$version\"/" \
        src/data/emacs-mode/agda2-mode.el

    # Update the tag in the deployment workflow
    sed -ri "s/--notes-start-tag v[0-9.]+/--notes-start-tag v$version/" deploy.yml

    sed -ri "s/^(VERSION\s+=\s+).*/\1$version/" mk/paths.mk

    sed -ri "s/\"Agda version [0-9.]+\"/\"Agda version $version\"/" \
        test/interaction/Issue1244a.out \
        test/interaction/Issue1244b.out
}

run () {
    "$@" || YesNoQuestion "Error: Command \`$*' failed. Abort?" || exit 1
}


srcdir=$(mktemp -d --tmpdir "Agda-XXXXXX")
trap 'rm -rf -- "$srcdir"' EXIT

url=https://github.com/agda/agda
git clone "$url" "$srcdir"
cd "$srcdir"

version=$( sed -rn '/^version:\s*([0-9]+\.[0-9]+)\.([0-9]+)(\.[0-9]+)?\s*$/ {s//\1 \2/p; q}' Agda.cabal \
         | { read -r maj min; echo "$maj.$(( 1 + min))"; } )
version=$( Question "Release version number?" "$version" )
echo "$version" | grep -Eqx "[0-9]+(\.[0-9]+){2,3}" || { echo "Bad version number: $version" >&2; exit 1; }
echo "$version" | grep -Eqx "[0-9]+(\.[0-9]+){2}" && maint=${version##*.} || maint=0

notes=doc/release-notes/$( echo "$version" | tr . - ).txt
! YesNoQuestion "Edit release notes (in $notes)?" || edit "$notes"
! YesNoQuestion "Update README.md?"    n          || edit README.md
! YesNoQuestion "Update LICENSE file?" n          || edit LICENSE


updateVersion "$version"
git add -v Agda.cabal \
           src/data/emacs-mode/agda2-mode.el \
           mk/paths.mk \
           test/interaction/Issue1244a.out \
           test/interaction/Issue1244b.out

# Add a second source-repository section to Agda.cabal:
cat >> Agda.cabal <<-EOF

	source-repository this
	  type:     git
	  location: $url
	  tag:      $version
EOF

# Remove -Werror from Agda.cabal
#
# (Agda uses code generated by Cabal, Paths_Agda, and under some
# configurations this code gives rise to warnings.)
sed -ri '/-Werror(\s.*)?$/ {
           s/^(\s+ghc-options:)\s+-Werror(\s.*)?$/\1\2/; t
            /^\s+-Werror\s*$/d
         }' Agda.cabal

# Ensure that cabal haddock works
cabal sandbox init
cabal update
cabal install --only-dependencies -j
cabal install alex haddock -j
cabal configure
run cabal haddock

# Ensure that the Emacs mode can be compiled without errors or
# warnings (except for the "cl package required at runtime" warning):
find "src/data/emacs-mode" -type f -name '*.el' -print0 \
| xargs -r0 emacs --batch -L "src/data/emacs-mode" -f batch-byte-compile
find "src/data/emacs-mode" -type f -name '*.elc' -delete

cabal sdist
cabal check
cabal install

AGDA_BIN="$(pwd)/.cabal-sandbox/bin/agda"
export AGDA_BIN

make install-fix-agda-whitespace
run make test

# Ensure that all the packages build properly.
testdir=$(mktemp -d --tmpdir "Agda-XXXXXX-$version")
trap 'rm -rf -- "$srcdir" "$testdir"' EXIT
cd "$testdir"
tar -xz --strip-components=1 -f "$srcdir/dist/Agda-$version.tar.gz"

cabal sandbox init
cabal update
cabal install --only-dependencies -j
cabal configure
cabal install

AGDA_BIN="$(pwd)/.cabal-sandbox/bin/agda"
export AGDA_BIN

stdlib=std-lib
git clone https://github.com/agda/agda-stdlib "$stdlib"
cd "$stdlib"
cabal sandbox --sandbox=../.cabal-sandbox init
make Everything.agda
cd "$srcdir"

# XXX Do not forget to test the Emacs mode.

git diff-index --cached --quiet HEAD || git commit -vm "Preparing new release ($version)."
git tag "$version"
git push --tags HEAD
git restore Agda.cabal

cabal upload "dist/Agda-$version.tar.gz"

# XXX Update the Agda Wiki.
# XXX Announce the release of the new version on the Agda mailing list.

[ $maint = 0 ] && maintv="$version" || maintv="${version%.*}"
git switch -c "maint-$maintv"
updateVersion "${maintv}.$(( maint + 1 ))"

sed -ri 's/^#\s*(override CABAL_OPTS\+=--program-suffix=-\$\(VERSION\))$/\1/' Makefile
git add Makefile
git commit -vm "Release ${maintv}.$(( maint + 1))."

git switch master
git merge "maint-$version"

if [ $maint = 0 ]; then
    # new major release
    git rm "$notes"
    notes=doc/release-notes/$( echo "${version%.*}.$(( 1 + ${version##*.}))" | tr . - ).txt
    cp -f template.txt "$notes"
    sed -ri "s/\bX\.Y\.Z\b/$version/" "$notes"
    sed -ri "s/^(\s+)-\smaster$/&\n\1- maint-$maintv/" .travis.yml
    git add -v .travis.yml "$notes"
    git commit -vm "Release $version."
fi

git push
git switch "maint-$version"
git push -u origin "maint-$version"
