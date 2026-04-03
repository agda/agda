from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable

@dataclass(frozen=True)
class ResourceVector:
    n: int = 0  # normalization debt
    u: int = 0  # unification/search frontier
    m: int = 0  # unsolved metas
    i: int = 0  # invalidation breadth
    r: int = 0  # recomputation mass
    d: int = 0  # divergence risk

    def potential(self) -> float:
        return (
            1.0 * self.n +
            1.2 * self.u +
            2.0 * self.m +
            0.8 * self.i +
            1.0 * self.r +
            2.5 * self.d
        )

@dataclass(frozen=True)
class Strategy:
    name: str
    delta: ResourceVector
    risk: float

    def expected_score(self, state: ResourceVector) -> float:
        next_state = ResourceVector(
            n=max(0, state.n + self.delta.n),
            u=max(0, state.u + self.delta.u),
            m=max(0, state.m + self.delta.m),
            i=max(0, state.i + self.delta.i),
            r=max(0, state.r + self.delta.r),
            d=max(0, state.d + self.delta.d),
        )
        return state.potential() - next_state.potential() - self.risk

INTRO = Strategy("intro", ResourceVector(m=-1), risk=0.10)
TRIVIAL = Strategy("trivial", ResourceVector(n=-1, m=-1, d=-1), risk=0.05)
REWRITE = Strategy("rewrite", ResourceVector(n=-2, u=1), risk=0.30)
APPLY = Strategy("apply", ResourceVector(m=-1, u=1), risk=0.50)
CASE = Strategy("case", ResourceVector(i=2, d=1), risk=1.00)
CONSTRUCTOR = Strategy("constructor", ResourceVector(m=-1, u=0), risk=0.20)

ALL_STRATEGIES = [INTRO, TRIVIAL, REWRITE, APPLY, CASE, CONSTRUCTOR]

def classify_goal(goal_type: str) -> list[Strategy]:
    gt = goal_type.lower()
    if "->" in gt or "∀" in gt or "pi" in gt:
        return [INTRO, TRIVIAL, APPLY]
    if "≡" in goal_type or "=" in goal_type:
        return [REWRITE, TRIVIAL, APPLY]
    if any(tok in gt for tok in ["data", "nat", "vec", "list", "maybe"]):
        return [CONSTRUCTOR, APPLY, TRIVIAL]
    return [APPLY, TRIVIAL, REWRITE, CASE]

def choose_strategy(goal_type: str, state: ResourceVector) -> Strategy:
    candidates = classify_goal(goal_type)
    return max(candidates, key=lambda s: s.expected_score(state))
