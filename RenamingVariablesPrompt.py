#!/usr/bin/env python3

from __future__ import annotations
import argparse
import subprocess
import sys
from pathlib import Path


def build_prompt(lean_file: str, style_file: str, report_file: str) -> str:
    return f"""You are an expert Lean 4 developer tasked with refactoring code to strictly comply with documented naming standards.

Follow these steps exactly:

STEP 1 — Rule Extraction
Read {style_file} line 9 to 24.
Use ONLY the rules stated in that section.
For usual mathematical notations, use the conventional upper case letter.

STEP 2 — Violation Detection
Scan {lean_file}.
Identify all variable binders (explicit or implicit), including:
- ∀ binders
- λ / fun parameters
- let bindings
- match pattern binders
- section variables
- structure field variables

For each variable, determine whether it strictly violates one of the extracted rules.
Do not flag variables that comply.

STEP 3 — Rename Planning
Create a mapping:

old_name → new_name

Rules:
- The new name must strictly satisfy the violated rule.
- No semantic meaning may change.
- No name collisions within the same scope.
- Do not rename variables unnecessarily.
- Preserve consistent renaming across the file.

STEP 4 — Execution
Modify {lean_file} directly.
- Make no unrelated edits.
- Preserve formatting and structure.

STEP 5 — Reporting
Write a brief section summarizing the rules applied in {report_file}, in a section titled "{lean_file}".
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("lean_file", help="Lean file to refactor")
    parser.add_argument("--style", default="style.md", help="Style file")
    parser.add_argument("--report", default="RenamingVariables.md", help="Report file")
    parser.add_argument("--model", default="opus", help="Claude model")
    args = parser.parse_args()

    prompt = build_prompt(args.lean_file, args.style, args.report)

    cmd = [
        "claude",
        "-p",
        prompt,
        "--model",
        args.model,
        "--no-session-persistence",
        "--allowedTools",
        "Read,Edit,Grep,Glob,Bash",
    ]

    try:
        return subprocess.run(cmd).returncode
    except FileNotFoundError:
        print("ERROR: 'claude' CLI not found on PATH.", file=sys.stderr)
        return 127


if __name__ == "__main__":
    raise SystemExit(main())