from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Sequence
import hashlib

from .scheduler import ResourceVector

@dataclass
class GuardDecision:
    stop: bool
    reason: str

class DivergenceGuard:
    def __init__(self, max_history: int = 32, growth_limit: int = 3,
                 max_search_frontier: int = 25, max_divergence: int = 10):
        self.max_history = max_history
        self.growth_limit = growth_limit
        self.max_search_frontier = max_search_frontier
        self.max_divergence = max_divergence
        self.signatures: list[str] = []
        self.potentials: list[float] = []

    def _signature(self, goal_type: str, state: ResourceVector, recent: Sequence[str]) -> str:
        payload = f"{goal_type}|{asdict(state)}|{tuple(recent[-4:])}"
        return hashlib.sha256(payload.encode()).hexdigest()

    def check(self, goal_type: str, state: ResourceVector, recent: Sequence[str]) -> GuardDecision:
        """Evaluate whether the current search state should stop.

        Invariants:
        - stop reasons are derived from explicit state thresholds or repeated signatures.
        - history windows remain bounded by `max_history`.
        """
        sig = self._signature(goal_type, state, recent)
        potential = state.potential()

        self.signatures.append(sig)
        self.signatures = self.signatures[-self.max_history:]
        self.potentials.append(potential)
        self.potentials = self.potentials[-self.max_history:]

        if self.signatures.count(sig) >= 2:
            return GuardDecision(True, "cycle_detected")

        if len(self.potentials) >= self.growth_limit:
            tail = self.potentials[-self.growth_limit:]
            if all(tail[i] < tail[i+1] for i in range(len(tail)-1)):
                return GuardDecision(True, "potential_growing")

        if state.u > self.max_search_frontier:
            return GuardDecision(True, "search_frontier_too_large")

        if state.d > self.max_divergence:
            return GuardDecision(True, "divergence_risk_too_large")

        return GuardDecision(False, "ok")
