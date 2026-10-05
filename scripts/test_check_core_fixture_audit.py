"""Exercise the CI gate with incomplete reports and failing audit processes."""

from contextlib import redirect_stderr, redirect_stdout
import hashlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import check_core_fixture_audit as audit


BASELINE_REPORT = """source=script_tests.json
tests=1222 compared=866 matched=866 mismatched=0 unsupported=356 documentation=51
unsupported.signature=129
unsupported.other=227
unsupported-detail.signature.script-pubkey=129
"""


class ReportTests(unittest.TestCase):
    def setUp(self):
        # Keep these synthetic reports stable when production coverage increases.
        floor_patch = patch.object(audit, "MINIMUM_MATCHED", 866)
        floor_patch.start()
        self.addCleanup(floor_patch.stop)

    def test_baseline_and_increased_coverage(self):
        audit.validate_report(BASELINE_REPORT)
        audit.validate_report(
            BASELINE_REPORT.replace("866", "867")
            .replace("356", "355").replace("227", "226")
        )

    def test_rejects_unusable_reports(self):
        cases = {
            "missing summary": "source=script_tests.json\n",
            "malformed summary": BASELINE_REPORT.replace("matched=866", "matched=bad"),
            "duplicate summary": BASELINE_REPORT + BASELINE_REPORT,
            "mismatch": BASELINE_REPORT.replace("matched=866", "matched=865")
                .replace("mismatched=0", "mismatched=1"),
            "coverage loss": BASELINE_REPORT.replace("866", "865")
                .replace("356", "357").replace("227", "228"),
            "changed fixture total": BASELINE_REPORT.replace("tests=1222", "tests=1221"),
            "changed documentation": BASELINE_REPORT.replace("documentation=51", "documentation=50"),
            "inconsistent compared": BASELINE_REPORT.replace("compared=866", "compared=867"),
            "inconsistent total": BASELINE_REPORT.replace("unsupported=356", "unsupported=355"),
            "missing categories": BASELINE_REPORT.replace("unsupported.other=227\n", ""),
            "malformed category": BASELINE_REPORT.replace("other=227", "other=bad"),
            "duplicate category": BASELINE_REPORT + "unsupported.other=0\n",
        }
        for name, report in cases.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit.validate_report(report)


class RunnerTests(unittest.TestCase):
    def setUp(self):
        floor_patch = patch.object(audit, "MINIMUM_MATCHED", 866)
        floor_patch.start()
        self.addCleanup(floor_patch.stop)
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.fixture = self.directory / "script_tests.json"
        self.fixture.write_bytes(b'[["sample fixture"]]\n')
        checksum = hashlib.sha256(self.fixture.read_bytes()).hexdigest()
        checksum_patch = patch.object(audit, "FIXTURE_SHA256", checksum)
        checksum_patch.start()
        self.addCleanup(checksum_patch.stop)
        self.executable = self.directory / "audit"
        self.write_executable(BASELINE_REPORT)
        self.stdout, self.stderr = io.StringIO(), io.StringIO()

    def write_executable(self, report, exit_code=0):
        self.executable.write_text(
            f"#!{sys.executable}\n"
            "import sys\n"
            "assert sys.argv[1] == '--show-details'\n"
            f"assert sys.argv[2] == {str(self.fixture)!r}\n"
            f"print({report!r}, end='')\n"
            f"sys.exit({exit_code})\n"
        )
        self.executable.chmod(0o755)

    def run_gate(self):
        with redirect_stdout(self.stdout), redirect_stderr(self.stderr):
            return audit.main([
                "--fixture", str(self.fixture),
                "--audit-executable", str(self.executable),
            ])

    def test_retains_full_report(self):
        self.assertEqual(self.run_gate(), 0)
        self.assertIn(BASELINE_REPORT, self.stdout.getvalue())

    def test_nonzero_exit_fails_even_with_valid_report(self):
        self.write_executable(BASELINE_REPORT, exit_code=7)
        self.assertEqual(self.run_gate(), 1)
        self.assertIn(BASELINE_REPORT, self.stdout.getvalue())
        self.assertIn("status 7", self.stderr.getvalue())

    def test_bad_report_fails_even_with_zero_exit(self):
        self.write_executable("source=script_tests.json\n")
        self.assertEqual(self.run_gate(), 1)
        self.assertIn("well-formed audit summary", self.stderr.getvalue())

    def test_checksum_corruption_prevents_execution(self):
        self.fixture.write_bytes(self.fixture.read_bytes() + b" ")
        with patch.object(audit.subprocess, "run") as execute:
            self.assertEqual(self.run_gate(), 1)
            execute.assert_not_called()
        self.assertIn("checksum mismatch", self.stderr.getvalue())

    def test_missing_fixture_fails(self):
        self.fixture.unlink()
        self.assertEqual(self.run_gate(), 1)
        self.assertIn("Core fixture audit failed", self.stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
