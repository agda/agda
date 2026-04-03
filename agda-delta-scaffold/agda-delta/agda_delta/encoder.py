from __future__ import annotations
import hashlib
import torch
import torch.nn as nn

EMBED_DIM = 128
NODE_TYPES = {"var": 0, "const": 1, "app": 2, "lam": 3, "pi": 4}

def tokenize_term(term: str) -> list[str]:
    for ch in "()[]{}:,→":
        term = term.replace(ch, " ")
    return [tok for tok in term.split() if tok]

def hashed_bow(term: str) -> torch.Tensor:
    vec = torch.zeros(EMBED_DIM)
    for tok in tokenize_term(term):
        idx = int(hashlib.sha256(tok.encode()).hexdigest(), 16) % EMBED_DIM
        vec[idx] += 1.0
    return vec / max(1, vec.sum())

class TermEncoder(nn.Module):
    def __init__(self):
        super().__init__()
        self.type_embed = nn.Embedding(len(NODE_TYPES), EMBED_DIM)
        self.combine = nn.Linear(EMBED_DIM * 2, EMBED_DIM)
        self.activation = nn.ReLU()

    def encode_node(self, node: dict) -> torch.Tensor:
        base = self.type_embed(torch.tensor(NODE_TYPES[node["type"]]))
        children = node.get("children", [])
        if not children:
            return base
        child_vecs = [self.encode_node(c) for c in children]
        agg = torch.mean(torch.stack(child_vecs), dim=0)
        return self.activation(self.combine(torch.cat([base, agg], dim=0)))

    def forward(self, node: dict) -> torch.Tensor:
        return self.encode_node(node)
