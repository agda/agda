from __future__ import annotations
from pathlib import Path
import os
import json
from typing import Any

class RewriteDB:
    def __init__(self, path: str | Path = "data/rewrites.json"):
        self.path = Path(path)
        self.max_rules = int(os.environ.get("AGDA_DELTA_REWRITE_DB_MAX_RULES", "2000"))
        if self.max_rules <= 0:
            self.max_rules = 2000
        self.rules: list[dict[str, Any]] = []

    def _trim_rules(self, rules: list[dict[str, Any]]) -> list[dict[str, Any]]:
        if self.max_rules <= 0 or len(rules) <= self.max_rules:
            return rules
        return rules[-self.max_rules :]

    def load(self) -> None:
        loaded: list[dict[str, Any]] = []
        if self.path.exists():
            loaded = json.loads(self.path.read_text(encoding="utf-8"))
            self.rules = self._trim_rules(loaded)
        else:
            self.rules = []
        if self.path.exists() and len(self.rules) != len(loaded):
            self.save()

    def save(self) -> None:
        self.path.write_text(json.dumps(self.rules, indent=2), encoding="utf-8")

    def add(self, lhs: str, rhs: str, tag: str = "") -> None:
        self.rules = self._trim_rules(self.rules + [{"lhs": lhs, "rhs": rhs, "tag": tag}])
        self.save()

    def match(self, term: str) -> list[dict[str, Any]]:
        hits: list[dict[str, Any]] = []
        for rule in self.rules:
            if rule["lhs"] in term or rule["rhs"] in term:
                hits.append(rule)
        return hits
