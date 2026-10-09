#!/usr/bin/env python3
"""Check C test registration, fixture reachability, and proof hygiene.

This is a structural audit. Isabelle builds are the authority for correctness.
"""

import json
import re
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent


def audit():
    errors = []
    manifest = json.loads(
        (REPO / "design-documents" / "c-parity-manifest.json").read_text()
    )
    for directory in ("Micro_C_Parser_Tests", "Micro_C_Examples"):
        folder = REPO / directory
        root = (folder / "ROOT").read_text()
        registered = re.findall(r"^\s+([A-Za-z][A-Za-z0-9_]*)\s*$", root, re.M)
        theories = sorted(folder.glob("*.thy"))
        for theory in theories:
            if registered.count(theory.stem) != 1:
                errors.append(f"{theory.relative_to(REPO)} must occur once in ROOT")
            text = theory.read_text()
            if not re.search(r"\btheory\s+" + re.escape(theory.stem) + r"\b", text):
                errors.append(f"{theory.relative_to(REPO)} has the wrong theory name")
            if re.search(
                r"\b(sorry|oops|quick_and_dirty|Skip_Proof|skip_proofs)\b", text
            ):
                errors.append(f"{theory.relative_to(REPO)} contains a proof bypass")
        corpus = "\n".join(theory.read_text() for theory in theories)
        for fixture in sorted(folder.glob("*")):
            if fixture.suffix in (".c", ".txt") and fixture.name not in corpus:
                errors.append(f"{fixture.relative_to(REPO)} is an unused fixture")

    suite = manifest["regression_suite"]
    root = (REPO / suite["directory"] / "ROOT").read_text()
    if not re.search(r"\bsession\s+" + re.escape(suite["session"]) + r"\s*=", root):
        errors.append("C regression session disagrees with the coverage manifest")
    covered = set()
    for layer, names in suite["layers"].items():
        for name in names:
            covered.add(name)
            if not (REPO / suite["directory"] / f"{name}.thy").is_file():
                errors.append(f"coverage layer {layer!r} references absent theory {name}")
    actual = {path.stem for path in (REPO / suite["directory"]).glob("*.thy")}
    for name in sorted(actual - covered):
        errors.append(f"test theory {name} is missing from the coverage manifest")

    return errors


if __name__ == "__main__":
    failures = audit()
    if failures:
        raise SystemExit("\n".join(failures))
    print("C test registration, fixtures, coverage map, and proof hygiene: PASS")
