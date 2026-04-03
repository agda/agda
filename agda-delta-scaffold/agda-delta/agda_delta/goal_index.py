from __future__ import annotations
from dataclasses import dataclass
import os
from pathlib import Path
import json
import re
from typing import Any

@dataclass
class LemmaRecord:
    name: str
    type: str
    head: str
    tags: list[str]

class GoalIndex:
    def __init__(self, path: str | Path = "data/goals.jsonl", max_entries: int | None = None):
        self.path = Path(path)
        self.max_entries = (
            int(os.environ.get("AGDA_DELTA_GOAL_INDEX_MAX_ENTRIES", str(max_entries or 2000)))
            if max_entries is not None or "AGDA_DELTA_GOAL_INDEX_MAX_ENTRIES" in os.environ
            else 2000
        )
        if self.max_entries <= 0:
            self.max_entries = 2000
        self.lemmas: list[dict[str, Any]] = []
        self._rebuilding = False

    def _trim_records(self, records: list[dict[str, Any]]) -> list[dict[str, Any]]:
        if self.max_entries <= 0 or len(records) <= self.max_entries:
            return records
        return records[-self.max_entries :]

    def _rewrite_jsonl(self, records: list[dict[str, Any]]) -> None:
        if not records:
            self.path.write_text("", encoding="utf-8")
            return
        tmp = self.path.with_suffix(self.path.suffix + ".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            for record in records:
                f.write(json.dumps(record))
                f.write("\n")
        tmp.replace(self.path)

    def load(self) -> None:
        records: list[dict[str, Any]] = []
        if not self.path.exists():
            self.lemmas = []
        else:
            with self.path.open("r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    records.append(json.loads(line))
            self.lemmas = self._trim_records(records)
            if len(records) != len(self.lemmas):
                self.path.parent.mkdir(parents=True, exist_ok=True)
                self._rewrite_jsonl(self.lemmas)
            if not self.lemmas:
                return

    def add(self, name: str, type_: str, head: str, tags: list[str] | None = None) -> None:
        record = {
            "name": name,
            "type": type_,
            "head": head,
            "tags": tags or [],
        }
        records = self.lemmas + [record]
        self.lemmas = self._trim_records(records)
        if self._rebuilding:
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if len(records) > self.max_entries:
            self._rewrite_jsonl(self.lemmas)
        else:
            with self.path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(record))
                f.write("\n")

    def _apply_pruned_rebuild(self) -> None:
        self.lemmas = self._trim_records(self.lemmas)

    def rebuild_from_project(self, project_root: str | Path) -> None:
        """Rebuild the lemma index from a project tree.

        Preconditions:
        - `project_root` exists and is readable.

        Postconditions:
        - in-memory and on-disk index contents are regenerated from project files only.
        """
        root = Path(project_root).resolve()
        self.lemmas.clear()
        self._rebuilding = True
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if self.path.exists():
            self.path.unlink()
        for path in sorted(root.rglob("*.agda")):
            self._index_file(path)
        self._apply_pruned_rebuild()
        self._rewrite_jsonl(self.lemmas)
        self._rebuilding = False

    def _index_file(self, path: Path) -> None:
        """Index simple top-level type signatures from one file.

        Invariant:
        - signature extraction is best-effort and deterministic for fixed file text.
        """
        text = path.read_text(encoding="utf-8")
        matches = re.finditer(r"^([A-Za-z0-9_']+)\s*:\s*(.+)$", text, re.MULTILINE)
        for match in matches:
            name = match.group(1)
            type_ = " ".join(match.group(2).split())
            head = type_.split()[0] if type_.split() else name
            tags = [token for token in re.split(r"[^A-Za-z0-9_']+", type_) if token]
            self.add(name=name, type_=type_, head=head, tags=tags[:8])

    def retrieve(self, goal_type: str, limit: int = 10) -> list[dict[str, Any]]:
        """Return deterministically ranked lemma candidates for a goal."""
        gt = goal_type.lower()
        scored: list[tuple[int, dict[str, Any]]] = []
        for lemma in self.lemmas:
            score = 0
            if lemma["head"].lower() in gt:
                score += 5
            for tag in lemma.get("tags", []):
                if tag.lower() in gt:
                    score += 2
            shared = set(gt.split()) & set(lemma["type"].lower().split())
            score += len(shared)
            if score > 0:
                scored.append((score, lemma))
        scored.sort(key=lambda x: x[0], reverse=True)
        return [lemma for _, lemma in scored[:limit]]
