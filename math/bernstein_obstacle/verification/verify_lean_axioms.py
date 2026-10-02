#!/usr/bin/env python3
"""Check every requested declaration against a closed axiom whitelist.

This verifies a successful Lean audit transcript, not mathematical faithfulness
or a Lean exit code. The caller must separately require the Lean process to pass.
Only the pinned Lean '#print axioms' output format is accepted.
"""

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUEST = re.compile(r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$", re.MULTILINE)
REPORT = re.compile(
    r"'(?P<name>[^'\r\n]+)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\[\]]*)\]"
    r"|does not depend on any axioms)",
    re.DOTALL,
)


class AuditError(ValueError):
    """The transcript does not prove the requested closed-whitelist check."""


def verify(driver: str, transcript: str, expected_count: int | None = None) -> int:
    requests = REQUEST.findall(driver)
    if not requests:
        raise AuditError("the driver has no supported #print axioms requests")
    unsupported = [line for line in driver.splitlines()
                   if line.lstrip().startswith("#print") and not REQUEST.fullmatch(line)]
    if unsupported:
        raise AuditError("unsupported #print command in audit driver")
    repeated = [name for name, count in Counter(requests).items() if count != 1]
    if repeated:
        raise AuditError(f"duplicate requests: {', '.join(sorted(repeated))}")
    if expected_count is not None and len(requests) != expected_count:
        raise AuditError(f"expected {expected_count} requests, found {len(requests)}")

    reports = []
    offset = 0
    for match in REPORT.finditer(transcript):
        if transcript[offset:match.start()].strip():
            raise AuditError("unexpected or malformed output before an axiom report")
        offset = match.end()
        name = match.group("name")
        raw_axioms = match.group("axioms")
        axioms = [] if raw_axioms is None or not raw_axioms.strip() else [
            axiom.strip() for axiom in raw_axioms.split(",")
        ]
        if any(not axiom for axiom in axioms):
            raise AuditError(f"malformed axiom list for {name}")
        forbidden = set(axioms) - ALLOWED_AXIOMS
        if forbidden:
            raise AuditError(f"forbidden axioms for {name}: {', '.join(sorted(forbidden))}")
        reports.append(name)
    if transcript[offset:].strip():
        raise AuditError("unexpected or malformed output after the last axiom report")
    repeated_reports = [name for name, count in Counter(reports).items() if count != 1]
    if repeated_reports:
        raise AuditError(f"duplicate reports: {', '.join(sorted(repeated_reports))}")
    missing = set(requests) - set(reports)
    extra = set(reports) - set(requests)
    if missing or extra:
        raise AuditError(f"report mismatch: missing={sorted(missing)}, extra={sorted(extra)}")
    return len(requests)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("driver", type=Path)
    parser.add_argument("transcript", type=Path)
    parser.add_argument("--expected-count", type=int)
    args = parser.parse_args()
    try:
        count = verify(args.driver.read_text(encoding="utf-8-sig"),
                       args.transcript.read_text(encoding="utf-8-sig"),
                       args.expected_count)
    except (AuditError, OSError, UnicodeError) as error:
        print(f"axiom audit FAILED: {error}", file=sys.stderr)
        return 1
    print(f"axiom audit passed: {count} unique requests and reports; "
          f"allowed axioms: {', '.join(sorted(ALLOWED_AXIOMS))}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
