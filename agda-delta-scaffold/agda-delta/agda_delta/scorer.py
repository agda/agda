from __future__ import annotations
import torch

def rank_candidates(query_vec: torch.Tensor, candidate_vecs: list[torch.Tensor]) -> list[int]:
    scores = [torch.dot(query_vec, c).item() for c in candidate_vecs]
    return sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
