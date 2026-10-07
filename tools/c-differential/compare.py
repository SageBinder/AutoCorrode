#!/usr/bin/env python3
"""Normalize and compare AutoCorrode/C differential observations."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ORACLE_NAME_MAP = {
    "c_diff_const": "DiffUnit.diff_const",
    "c_diff_add": "DiffUnit.diff_add",
    "c_diff_choose": "DiffUnit.diff_choose",
    "c_diff_and": "DiffUnit.diff_and",
    "c_diff_signed_add": "DiffUnit.diff_signed_add",
    "c_diff_div": "DiffUnit.diff_div",
    "c_diff_shl": "DiffUnit.diff_shl",
    "diff32_abi_pointer_bits": "Diff32.abi_pointer_bits",
    "diff32_abi_long_bits": "Diff32.abi_long_bits",
    "diff32_abi_big_endian": "Diff32.abi_big_endian",
    "diffbe_abi_pointer_bits": "DiffBE.abi_pointer_bits",
    "diffbe_abi_big_endian": "DiffBE.abi_big_endian",
}

NEUTRAL_NAME_MAP = {
    "Global_Store.ref": "State_References.ref",
    "urust_eval": "shallow_computation_eval",
}


def replace_identifier(text: str, old: str, new: str) -> str:
    pattern = rf"(?<![A-Za-z0-9_.]){re.escape(old)}(?![A-Za-z0-9_])"
    return re.sub(pattern, new, text)


def normalize(line: str, oracle: bool) -> str:
    line = line.strip()
    marker = line.find("ACDIFF|")
    if marker >= 0:
        line = line[marker:]
    line = " ".join(line.split())
    mappings = dict(NEUTRAL_NAME_MAP)
    if oracle:
        mappings.update(ORACLE_NAME_MAP)
    for old in sorted(mappings, key=len, reverse=True):
        line = replace_identifier(line, old, mappings[old])
    return line


def read_lines(path: Path, oracle: bool = False) -> list[str]:
    return sorted(
        normalize(line, oracle)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    )


def compare_lists(
    label: str, oracle_lines: list[str], current_lines: list[str]
) -> list[str]:
    differences: list[str] = []
    only_oracle = sorted(set(oracle_lines) - set(current_lines))
    only_current = sorted(set(current_lines) - set(oracle_lines))
    if len(oracle_lines) != len(current_lines):
        differences.append(
            f"{label}: count differs "
            f"(oracle={len(oracle_lines)}, current={len(current_lines)})"
        )
    for line in only_oracle:
        differences.append(f"{label}: oracle only: {line}")
    for line in only_current:
        differences.append(f"{label}: current only: {line}")
    return differences


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True, type=Path)
    parser.add_argument("--current", required=True, type=Path)
    parser.add_argument("--oracle-failures", required=True, type=Path)
    parser.add_argument("--current-failures", required=True, type=Path)
    parser.add_argument("--oracle-complete", choices=("0", "1"), required=True)
    parser.add_argument("--current-complete", choices=("0", "1"), required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    oracle_observations = read_lines(args.oracle, oracle=True)
    current_observations = read_lines(args.current)
    oracle_failures = read_lines(args.oracle_failures)
    current_failures = read_lines(args.current_failures)

    differences = compare_lists(
        "observation", oracle_observations, current_observations
    )
    differences.extend(
        compare_lists("failure", oracle_failures, current_failures)
    )
    oracle_complete = args.oracle_complete == "1"
    current_complete = args.current_complete == "1"
    if not oracle_complete:
        differences.append("oracle observation build did not complete")
    if not current_complete:
        differences.append("current observation build did not complete")

    result = {
        "equal": not differences,
        "oracle_complete": oracle_complete,
        "current_complete": current_complete,
        "matched_observations": len(
            set(oracle_observations) & set(current_observations)
        ),
        "matched_failures": len(set(oracle_failures) & set(current_failures)),
        "oracle_observations": oracle_observations,
        "current_observations": current_observations,
        "oracle_failures": oracle_failures,
        "current_failures": current_failures,
        "differences": differences,
    }
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return 0 if result["equal"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
