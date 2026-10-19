#!/usr/bin/env python3

"""
Check that the files tracked by git do not have names that differ only by case.

Such clashes break checkouts on case-insensitive file systems (macOS, Windows).

1. Directories whose names differ only by case are reported.
   The correct spelling is determined by majority vote
   (number of tracked files under each spelling).
   A draw is resolved in favor of the spelling with more capital letters.

2. Files in the same directory whose names differ only by case are reported.
   The correct spelling is the one with more capital letters.

Clashes are reported in minimal form, e.g. if a/b/c/d.txt clashes with a/B/c/e.txt
this is reported as a clash between a/b and a/B.
For directory clashes, the files living under the wrong spelling are listed as well.

Exit code is 1 if there are clashes, 0 otherwise.
"""

import os
import subprocess
import sys
from collections import Counter, defaultdict

USE_COLOR = (sys.stdout.isatty() or "GITHUB_ACTIONS" in os.environ) and "NO_COLOR" not in os.environ
RED   = "\033[31m" if USE_COLOR else ""
GREEN = "\033[32m" if USE_COLOR else ""
RESET = "\033[0m"  if USE_COLOR else ""


def capitals(s):
    return sum(1 for c in s if c.isupper())


def pick_winner(counts):
    """Given a Counter of spellings, return the correct one:
    majority first, then more capitals, then lexicographically for determinism."""
    return max(counts, key=lambda s: (counts[s], capitals(s), s))


def join(*parts):
    return "/".join(p for p in parts if p)


def tracked_files():
    out = subprocess.run(["git", "ls-files", "-z"], check=True, stdout=subprocess.PIPE).stdout
    return [f.split("/") for f in out.decode("utf-8", "surrogateescape").split("\0") if f]


def find_clashes(files):
    """Return a list of (wrong, correct, files) triples,
    where files are the tracked files under the wrong spelling
    (empty for file clashes)."""
    clashes = []

    # Canonical spelling of each (original) directory prefix.
    canon = {(): ""}

    # Directories, level by level, so that clashes in subdirectories are
    # detected relative to the corrected spelling of their parents.
    depth = 1
    while True:
        votes = defaultdict(Counter)   # (canonical parent, lowercase name) -> spelling counts
        members = defaultdict(list)    # (canonical parent, name) -> files under it
        for parts in files:
            if len(parts) > depth:     # parts[depth-1] is a directory
                parent = canon[tuple(parts[:depth-1])]
                name = parts[depth-1]
                votes[(parent, name.lower())][name] += 1
                members[(parent, name)].append("/".join(parts))
        if not votes:
            break

        winners = {}
        for (parent, key), counts in sorted(votes.items()):
            winner = pick_winner(counts)
            winners[(parent, key)] = winner
            for name in sorted(counts):
                if name != winner:
                    clashes.append((join(parent, name), join(parent, winner),
                                    sorted(members[(parent, name)])))

        for parts in files:
            if len(parts) > depth:
                prefix = tuple(parts[:depth])
                if prefix not in canon:
                    parent = canon[prefix[:-1]]
                    canon[prefix] = join(parent, winners[(parent, prefix[-1].lower())])
        depth += 1

    # Files within the same (canonical) directory.
    names = defaultdict(set)   # (canonical dir, lowercase name) -> spellings
    for parts in files:
        d = canon[tuple(parts[:-1])]
        names[(d, parts[-1].lower())].add(parts[-1])
    for (d, key), spellings in sorted(names.items()):
        if len(spellings) > 1:
            winner = max(spellings, key=lambda s: (capitals(s), s))
            for name in sorted(spellings):
                if name != winner:
                    clashes.append((join(d, name), join(d, winner), []))

    return clashes


def main():
    clashes = find_clashes(tracked_files())
    if not clashes:
        print("✅ No case-insensitive filename clashes found.")
        return 0

    print("❌ Error: filenames differing only by case detected!")
    print("   These break checkouts on case-insensitive file systems.")
    print("   Please rename (- wrong, + correct):")
    print()
    for wrong, correct, culprits in clashes:
        print(f"{RED}- {wrong}{RESET}")
        print(f"{GREEN}+ {correct}{RESET}")
        for f in culprits:
            print(f"    {f}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
