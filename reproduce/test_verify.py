"""Small stdlib adversarial tests. No large archive, solver or finite census runs."""
import copy
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

import verify


def tar_bytes(entries):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
        for name, kind, body in entries:
            member = tarfile.TarInfo(name)
            member.type = kind
            if kind == tarfile.REGTYPE:
                member.size = len(body)
            elif kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                member.linkname = body.decode()
            archive.addfile(member, io.BytesIO(body) if kind == tarfile.REGTYPE else None)
    buffer.seek(0)
    return buffer


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="ramsey61-verifier-fixture-")
        self.root = Path(self.workspace.name).resolve()

    def tearDown(self):
        self.workspace.cleanup()  # Only these newly created test fixtures.

    def extract(self, entries, **kwargs):
        return verify.extract_archive(tar_bytes(entries), self.root / "new-snapshot",
                                      disk_guard=lambda *_: None, **kwargs)

    def test_good_ordinary_archive(self):
        result = self.extract([("a", tarfile.DIRTYPE, b""), ("a/data", tarfile.REGTYPE, b"evidence")])
        self.assertEqual(result["files"], 1)
        self.assertEqual((self.root / "new-snapshot/a/data").read_bytes(), b"evidence")

    def test_tampered_archive_hash(self):
        original = b"frozen archive"
        expected = (len(original), hashlib.sha256(original).hexdigest())
        with self.assertRaisesRegex(ValueError, "SHA256"):
            verify.archive_authenticate(io.BytesIO(b"frozen archivE"), expected)

    def test_lfs_pointer_is_not_archive(self):
        with self.assertRaisesRegex(ValueError, "Git LFS pointer"):
            verify.archive_authenticate(io.BytesIO(b"version https://git-lfs.github.com/spec/v1\n"))

    def test_parent_traversal(self):
        with self.assertRaisesRegex(ValueError, "Unsafe archive"):
            self.extract([("../escape", tarfile.REGTYPE, b"bad")])
        self.assertFalse((self.root / "escape").exists())

    def test_absolute_path(self):
        with self.assertRaisesRegex(ValueError, "Unsafe archive"):
            self.extract([("/escape", tarfile.REGTYPE, b"bad")])

    def test_backslash_path(self):
        with self.assertRaisesRegex(ValueError, "Unsafe archive"):
            self.extract([("a\\escape", tarfile.REGTYPE, b"bad")])

    def test_symlink(self):
        with self.assertRaisesRegex(ValueError, "links/devices"):
            self.extract([("link", tarfile.SYMTYPE, b"../escape")])

    def test_hardlink(self):
        with self.assertRaisesRegex(ValueError, "links/devices"):
            self.extract([("link", tarfile.LNKTYPE, b"../escape")])

    def test_fifo(self):
        with self.assertRaisesRegex(ValueError, "links/devices"):
            self.extract([("fifo", tarfile.FIFOTYPE, b"")])

    def test_duplicate_member(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            self.extract([("file", tarfile.REGTYPE, b"a"), ("file", tarfile.REGTYPE, b"b")])

    def test_file_directory_collision(self):
        with self.assertRaisesRegex(ValueError, "collision"):
            self.extract([("file", tarfile.REGTYPE, b"a"), ("file/child", tarfile.REGTYPE, b"b")])

    def test_payload_limit(self):
        with self.assertRaisesRegex(ValueError, "ceiling"):
            self.extract([("file", tarfile.REGTYPE, b"abcd")], max_bytes=3)

    def test_member_limit(self):
        with self.assertRaisesRegex(ValueError, "ceiling"):
            self.extract([("a", tarfile.REGTYPE, b""), ("b", tarfile.REGTYPE, b"")], max_members=1)

    def test_existing_destination_rejected(self):
        (self.root / "new-snapshot").mkdir()
        with self.assertRaisesRegex(ValueError, "already exist"):
            self.extract([])

    def test_pinned_metadata_tamper(self):
        path = self.root / "metadata.json"
        path.write_bytes(b"{}")
        with self.assertRaisesRegex(ValueError, "Pinned metadata differs"):
            verify.pinned_bytes(path, (2, "0" * 64))

    def test_symlink_input_rejected(self):
        path = self.root / "regular"
        path.write_bytes(b"a")
        (self.root / "link").symlink_to(path)
        with self.assertRaisesRegex(ValueError, "Nonordinary"):
            verify.fingerprint(self.root / "link")

    def test_receipt_cannot_be_in_evidence(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            verify.outside(self.root / "snapshot/receipt.json", self.root / "snapshot")

    def test_full_census_count_tamper(self):
        result = {"status": "PASS_STAGING_BYTES_AND_CUSTODY", "total_files": verify.EXPECTED_FILES,
                  "total_bytes": verify.EXPECTED_BYTES, "manifest_index_sha256": verify.INDEX_PIN[1],
                  "new_solver_calls": 0, "original_source_reads": 0,
                  "custody": {"status": "PASS_STAGED_C_AND_FINAL_CUSTODY", "effective_dual_native_owners": 456,
                              "native_logs": 1843, "formal_certificate_verified": False,
                              "result_counts": {"restricted": 914, "original_broad": 912, "first_tail": 13, "second_tail": 4}}}
        verify.check_verifier_result(result)
        bad = copy.deepcopy(result)
        bad["total_files"] -= 1
        with self.assertRaisesRegex(ValueError, "Unexpected full"):
            verify.check_verifier_result(bad)
        bad = copy.deepcopy(result)
        bad["custody"]["result_counts"]["second_tail"] = 3
        with self.assertRaisesRegex(ValueError, "Unexpected custody"):
            verify.check_verifier_result(bad)

    def test_edge_numbering_boundaries(self):
        self.assertEqual(verify.edge_var(0, 1, 0), 1)
        self.assertEqual(verify.edge_var(59, 60, 3), 7320)

    def c_all_fixture(self):
        """Synthetic byte-recipe fixture, not a mathematical CNF claim."""
        seeds = {"count": 456, "seeds": [{"id": "R3_%03d" % i,
                  "unit_colors": [[0, 1, 0]], "non_color": []} for i in range(456)]}
        body = b"1 0\n"
        base = b"p cnf 439723 1880888\n" + body
        expected = hashlib.sha256(b"p cnf 439723 1880889\n" + body + b"1 0\n").hexdigest()
        accepted = {"status": "PASS_ALL456_BROADER_DUAL_NATIVE_UNSAT", "effective_dual_native_UNSAT": 456,
                    "unresolved": [], "effective_acceptance_records": [
                        {"id": "R3_%03d" % i, "formula_sha256": expected} for i in range(456)]}
        return seeds, base, accepted

    def run_c_all_fixture(self, seeds, base, accepted):
        contents = {"inputs/SEEDS.json": json.dumps(seeds).encode(), "inputs/BROAD_BASE_001.cnf": base,
                    "reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json": json.dumps(accepted).encode()}
        pins = {}
        for relative, data in contents.items():
            path = self.root / verify.C / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            pins[relative] = (len(data), hashlib.sha256(data).hexdigest())
        with mock.patch.dict(verify.C_PINS, pins):
            return verify.verify_c_all(self.root)

    def test_c_all_shared_prefix_hashes(self):
        self.assertEqual(self.run_c_all_fixture(*self.c_all_fixture())["formulas"], 456)

    def test_c_all_missing_last_seed(self):
        seeds, base, accepted = self.c_all_fixture()
        seeds["seeds"].pop()
        with self.assertRaisesRegex(ValueError, "Seed census differs"):
            self.run_c_all_fixture(seeds, base, accepted)

    def test_c_all_bad_last_formula_hash(self):
        seeds, base, accepted = self.c_all_fixture()
        accepted["effective_acceptance_records"][-1]["formula_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Reconstructed formula differs: R3_455"):
            self.run_c_all_fixture(seeds, base, accepted)

    def test_c_all_unresolved_not_accepted(self):
        seeds, base, accepted = self.c_all_fixture()
        accepted["unresolved"] = ["R3_455"]
        with self.assertRaisesRegex(ValueError, "Accepted C census differs"):
            self.run_c_all_fixture(seeds, base, accepted)


if __name__ == "__main__":
    unittest.main(verbosity=2)
