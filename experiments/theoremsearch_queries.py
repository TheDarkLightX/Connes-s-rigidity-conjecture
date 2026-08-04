from __future__ import annotations

import json
import urllib.request
from pathlib import Path

ENDPOINT = "https://api.theoremsearch.com/search"
QUERIES = {
    "group_like_reconstruction": (
        "group-like elements of a group algebra are exactly the basis elements corresponding to group elements"
    ),
    "length_two_witt_coordinate": (
        "length two p-typical Witt vectors over the finite field F_p are isomorphic to integers modulo p squared"
    ),
    "ternary_degree_three_support": (
        "minimum Hamming weight or support size of a nonzero degree at most three polynomial function over F_3"
    ),
    "polynomial_tensor_orbit": (
        "nonzero symmetric tensor cube over F[t]^3 has infinite orbit under SL_3(F[t]) elementary transvections"
    ),
}


def query(text: str) -> dict:
    payload = json.dumps(
        {
            "query": text,
            "n_results": 10,
            "include_unknown_citations": True,
            "citation_weight": 0.05,
        }
    ).encode("utf-8")
    request = urllib.request.Request(
        ENDPOINT,
        data=payload,
        headers={"Content-Type": "application/json", "User-Agent": "connes-rigidity-research/0.1"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def main() -> None:
    results = {}
    for key, text in QUERIES.items():
        results[key] = {"query": text, "response": query(text)}
    output = {
        "service": "TheoremSearch",
        "endpoint": ENDPOINT,
        "claim_boundary": (
            "Semantic retrieval is prior-art evidence, not a proof of novelty or non-novelty; "
            "a domain expert must review the returned statements and citations."
        ),
        "queries": results,
    }
    path = Path("experiments/theoremsearch_results.json")
    path.write_text(json.dumps(output, sort_keys=True, indent=2), encoding="utf-8")
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
