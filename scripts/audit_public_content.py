#!/usr/bin/env python3
"""Fail closed on common publication leaks and stale internal references."""

from __future__ import annotations

import json
from html.parser import HTMLParser
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PUBLIC_FILES = [
    ROOT / "README.md",
    ROOT / "CITATION.cff",
    *sorted((ROOT / "docs").glob("*.md")),
    *sorted((ROOT / "paper").glob("*.md")),
    *sorted((ROOT / "site").glob("*")),
]

FORBIDDEN_TEXT = {
    "/home/": "absolute home-directory path",
    "/tmp/": "temporary local path",
    "/workspace/": "machine-local workspace path",
    "sandbox:/": "sandbox-only link",
    "/pull/": "pull-request link on a publication surface",
    "PR #": "pull-request shorthand on a publication surface",
    "\N{EM DASH}": "em dash prohibited by the writing convention",
    "\N{EN DASH}": "en dash prohibited by the writing convention",
}


class StrictEnoughHTMLParser(HTMLParser):
    """Use the standard parser to reject malformed entities and declarations."""

    def error(self, message: str) -> None:  # pragma: no cover, compatibility hook
        raise ValueError(message)


def audit_text(path: Path) -> list[str]:
    if not path.is_file():
        return [f"missing public file: {path.relative_to(ROOT)}"]
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    failures = []
    for needle, description in FORBIDDEN_TEXT.items():
        if needle in text:
            failures.append(f"{path.relative_to(ROOT)}: {description}")
    return failures


def audit_status() -> list[str]:
    path = ROOT / "site" / "status.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"site/status.json: invalid JSON: {exc}"]
    failures = []
    if not isinstance(data.get("claimBoundary"), str):
        failures.append("site/status.json: claimBoundary must be a string")
    lean = data.get("lean")
    if not isinstance(lean, dict):
        failures.append("site/status.json: lean must be an object")
    else:
        for field in ("moduleCount", "lastFailingModules", "trustBypasses", "finiteSuites"):
            if not isinstance(lean.get(field), int):
                failures.append(f"site/status.json: lean.{field} must be an integer")
    if not isinstance(data.get("claims"), list) or not data["claims"]:
        failures.append("site/status.json: claims must be a nonempty list")
    return failures


def audit_html() -> list[str]:
    path = ROOT / "site" / "index.html"
    try:
        text = path.read_text(encoding="utf-8")
        StrictEnoughHTMLParser().feed(text)
    except (OSError, ValueError) as exc:
        return [f"site/index.html: parse failed: {exc}"]
    required_ids = {
        "claim-boundary",
        "module-count",
        "failure-count",
        "trust-count",
        "suite-count",
        "claim-cards",
    }
    return [
        f"site/index.html: missing id={element_id!r}"
        for element_id in sorted(required_ids)
        if f'id="{element_id}"' not in text
    ]


def main() -> None:
    failures = []
    for path in PUBLIC_FILES:
        failures.extend(audit_text(path))
    failures.extend(audit_status())
    failures.extend(audit_html())
    if failures:
        raise SystemExit("Public-content audit failed:\n- " + "\n- ".join(failures))
    print(f"Public-content audit passed for {len(PUBLIC_FILES)} files.")


if __name__ == "__main__":
    main()
