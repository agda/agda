from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
import re

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.']+)\s+where\b", re.MULTILINE)
IMPORT_RE = re.compile(r"^\s*open\s+import\s+([A-Za-z0-9_.']+)|^\s*import\s+([A-Za-z0-9_.']+)", re.MULTILINE)


@dataclass(frozen=True)
class AgdaFile:
    path: Path
    module_name: str
    imports: tuple[str, ...]


def _module_name_from_path(project_root: Path, path: Path) -> str:
    rel = path.relative_to(project_root).with_suffix("")
    return ".".join(rel.parts)


def parse_agda_file(project_root: Path, path: Path) -> AgdaFile:
    text = path.read_text(encoding="utf-8")
    module_match = MODULE_RE.search(text)
    module_name = module_match.group(1) if module_match else _module_name_from_path(project_root, path)
    imports: list[str] = []
    for match in IMPORT_RE.finditer(text):
        imported = match.group(1) or match.group(2)
        if imported:
            imports.append(imported)
    return AgdaFile(path=path, module_name=module_name, imports=tuple(imports))


def scan_project(project_root: str | Path) -> list[AgdaFile]:
    """Return the canonical set of `.agda` files under `project_root`.

    Preconditions:
    - `project_root` exists.

    Postconditions:
    - returned entries are sorted by path for deterministic downstream ordering.
    """
    root = Path(project_root).resolve()
    if not root.exists():
        raise FileNotFoundError(f"project root does not exist: {root}")
    files = sorted(root.rglob("*.agda"))
    return [parse_agda_file(root, path) for path in files]


def solve_order(project_root: str | Path) -> list[Path]:
    """Produce a deterministic solve order.

    Invariants:
    - a fixed project tree yields a fixed order.
    - cycles do not crash ordering; unresolved remainder is appended in path order.

    Postconditions:
    - returns all discovered `.agda` files exactly once.
    """
    entries = scan_project(project_root)
    if not entries:
        raise FileNotFoundError(f"no .agda files found under: {Path(project_root).resolve()}")
    by_module = {entry.module_name: entry for entry in entries}
    indegree: dict[str, int] = {entry.module_name: 0 for entry in entries}
    forward: dict[str, list[str]] = defaultdict(list)

    for entry in entries:
        for imported in entry.imports:
            if imported in by_module:
                forward[imported].append(entry.module_name)
                indegree[entry.module_name] += 1

    ready = deque(sorted(module for module, degree in indegree.items() if degree == 0))
    ordered: list[Path] = []
    seen: set[str] = set()

    while ready:
        module_name = ready.popleft()
        if module_name in seen:
            continue
        seen.add(module_name)
        ordered.append(by_module[module_name].path)
        for dependent in sorted(forward[module_name]):
            indegree[dependent] -= 1
            if indegree[dependent] == 0:
                ready.append(dependent)

    if len(ordered) != len(entries):
        remaining = sorted(entry.path for entry in entries if entry.module_name not in seen)
        ordered.extend(remaining)

    return ordered
