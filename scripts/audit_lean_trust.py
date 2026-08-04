#!/usr/bin/env python3
"""Reject unchecked Lean escape hatches in the repository's source files."""

from __future__ import annotations

import argparse
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe)\b|\bsorryAx\b")
NATIVE_DECIDE = re.compile(r"\bnative_decide\b")


def mask_comments_and_strings(source: str) -> str:
    """Replace comments and strings with spaces while preserving line numbers."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False

    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]

        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            if char == "\\" and index + 1 < len(source):
                output.extend("  ")
                index += 2
            elif char == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if pair == "--":
            newline = source.find("\n", index)
            if newline == -1:
                output.extend(" " * (len(source) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        elif pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1

    return "".join(output)


def locations(path: pathlib.Path, pattern: re.Pattern[str]) -> list[str]:
    masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
    found: list[str] = []
    for line_number, line in enumerate(masked.splitlines(), start=1):
        if pattern.search(line):
            found.append(f"{path.relative_to(ROOT)}:{line_number}")
    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--allow-native-decide",
        action="store_true",
        help="report native_decide without rejecting it",
    )
    args = parser.parse_args()

    lean_files = [ROOT / "LeanMathlib.lean", *sorted((ROOT / "LeanMathlib").rglob("*.lean"))]
    forbidden = [item for path in lean_files for item in locations(path, FORBIDDEN)]
    native = [item for path in lean_files for item in locations(path, NATIVE_DECIDE)]

    if forbidden:
        print("Rejected unchecked Lean declarations:")
        print("\n".join(f"  {item}" for item in forbidden))

    if native:
        label = "Reported" if args.allow_native_decide else "Rejected"
        print(f"{label} compiler-trusting native_decide uses:")
        print("\n".join(f"  {item}" for item in native))

    if forbidden or (native and not args.allow_native_decide):
        return 1

    print(f"Lean trust scan passed for {len(lean_files)} source files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
