#!/usr/bin/env python3
"""Run the complete pinned Core fixture audit and enforce its coverage floor."""

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request


CORE_REVISION = "9be056a8a72b624dae9623b2f7bded92c2a21c91"
FIXTURE_SHA256 = "bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5"
FIXTURE_URL = (
    f"https://raw.githubusercontent.com/bitcoin/bitcoin/{CORE_REVISION}"
    "/src/test/data/script_tests.json"
)
EXPECTED_TESTS = 1222
EXPECTED_DOCUMENTATION = 51
# Every executable row in the pinned fixture must match.
MINIMUM_MATCHED = EXPECTED_TESTS
REPOSITORY = Path(__file__).resolve().parent.parent

SUMMARY = re.compile(
    r"tests=(\d+) compared=(\d+) matched=(\d+) mismatched=(\d+) "
    r"unsupported=(\d+) documentation=(\d+)"
)
UNSUPPORTED = re.compile(r"unsupported\.([a-z][a-z0-9-]*)=(\d+)")


def validate_report(report: str) -> None:
    """Reject incomplete, inconsistent, mismatching or regressed audit output."""
    summaries = [line for line in report.splitlines() if line.startswith("tests=")]
    if len(summaries) != 1 or not (summary := SUMMARY.fullmatch(summaries[0])):
        raise ValueError("expected exactly one well-formed audit summary")
    tests, compared, matched, mismatched, unsupported, documentation = map(
        int, summary.groups()
    )
    if tests != EXPECTED_TESTS or documentation != EXPECTED_DOCUMENTATION:
        raise ValueError(
            f"fixture row counts changed: expected {EXPECTED_TESTS} tests and "
            f"{EXPECTED_DOCUMENTATION} documentation rows"
        )
    if compared != matched + mismatched or tests != compared + unsupported:
        raise ValueError("audit summary row counts are inconsistent")
    if mismatched != 0:
        raise ValueError(f"audit has {mismatched} mismatched fixtures")
    if matched < MINIMUM_MATCHED:
        raise ValueError(
            f"coverage regressed: {matched} matched fixtures; "
            f"expected at least {MINIMUM_MATCHED}"
        )

    categories = {}
    for line in report.splitlines():
        if not line.startswith("unsupported."):
            continue
        category = UNSUPPORTED.fullmatch(line)
        if not category or category[1] in categories:
            raise ValueError("malformed or duplicate unsupported category")
        categories[category[1]] = int(category[2])
    if sum(categories.values()) != unsupported:
        raise ValueError("unsupported category counts do not match the summary")


def download_fixture(destination: Path) -> None:
    for attempt in range(3):
        try:
            with urllib.request.urlopen(FIXTURE_URL, timeout=60) as response:
                destination.write_bytes(response.read())
            return
        except (OSError, urllib.error.URLError) as error:
            if attempt == 2:
                raise
            print(f"fixture download failed: {error}; retrying", file=sys.stderr)
            time.sleep(attempt + 1)


def run_audit(fixture: Path, executable: Path) -> None:
    actual_digest = hashlib.sha256(fixture.read_bytes()).hexdigest()
    if actual_digest != FIXTURE_SHA256:
        raise ValueError(
            f"fixture checksum mismatch: expected {FIXTURE_SHA256}, got {actual_digest}"
        )
    print(f"core-revision={CORE_REVISION} sha256={actual_digest}", flush=True)
    result = subprocess.run(
        [str(executable.resolve()), "--show-details", str(fixture.resolve())],
        capture_output=True,
        text=True,
        check=False,
    )
    # Keep the complete unsupported category/detail report and mismatch evidence.
    print(result.stdout, end="", flush=True)
    print(result.stderr, end="", file=sys.stderr, flush=True)
    if result.returncode != 0:
        raise ValueError(f"audit executable exited with status {result.returncode}")
    validate_report(result.stdout)
    print(f"audit passed: at least {MINIMUM_MATCHED} matching fixtures, zero mismatches")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fixture", type=Path,
        help="use a local copy of the pinned fixture (the checksum is still checked)",
    )
    parser.add_argument(
        "--audit-executable", type=Path,
        default=REPOSITORY / ".lake/build/bin/core_fixture_audit",
        help="path to the built audit executable",
    )
    args = parser.parse_args(argv)
    try:
        if args.fixture is not None:
            run_audit(args.fixture, args.audit_executable)
        else:
            with tempfile.TemporaryDirectory(prefix="core-fixture-audit-") as directory:
                fixture = Path(directory) / "script_tests.json"
                download_fixture(fixture)
                run_audit(fixture, args.audit_executable)
    except (OSError, ValueError) as error:
        print(f"Core fixture audit failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
