from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SearchPolicy:
    goal_class: str
    max_candidates: int
    replay_all: bool
    stop_after_accept: bool = True


def classify_goal(goal_type: str) -> str:
    lowered = goal_type.lower()
    if "=" in goal_type or "≡" in goal_type:
        return "equality"
    if "→" in goal_type or "->" in lowered or "forall" in lowered or "∀" in goal_type:
        return "function"
    if any(token in lowered for token in ["set", "prop", "type"]):
        return "type"
    return "data"


def policy_for_goal(goal_type: str) -> SearchPolicy:
    goal_class = classify_goal(goal_type)
    if goal_class == "equality":
        return SearchPolicy(
            goal_class=goal_class,
            max_candidates=4,
            replay_all=False,
        )
    if goal_class == "function":
        return SearchPolicy(
            goal_class=goal_class,
            max_candidates=3,
            replay_all=False,
        )
    if goal_class == "type":
        return SearchPolicy(
            goal_class=goal_class,
            max_candidates=2,
            replay_all=False,
        )
    return SearchPolicy(
        goal_class=goal_class,
        max_candidates=2,
        replay_all=False,
    )
