"""Independent small negative checks for the portable A/B/D byte reconstructor."""
import copy
import hashlib
from pathlib import Path
import tempfile
import unittest

import abd_inputs as target


class ABDTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="ramsey61-abd-fixture-")
        self.root = Path(self.workspace.name).resolve()
        (self.root / "payload").write_bytes(b"frozen")

    def tearDown(self):
        self.workspace.cleanup()  # Newly created synthetic fixtures only.

    def test_pinned_bytes(self):
        self.assertEqual(target.bound(self.root, "payload", hashlib.sha256(b"frozen").hexdigest(), 6), b"frozen")

    def test_bad_digest(self):
        with self.assertRaisesRegex(ValueError, "hash/size mismatch"):
            target.bound(self.root, "payload", "0" * 64)

    def test_bad_size(self):
        with self.assertRaisesRegex(ValueError, "hash/size mismatch"):
            target.bound(self.root, "payload", hashlib.sha256(b"frozen").hexdigest(), 7)

    def test_traversal(self):
        with self.assertRaisesRegex(ValueError, "Unsafe"):
            target.inside(self.root, "../elsewhere")

    def test_symlink(self):
        (self.root / "link").symlink_to(self.root / "payload")
        with self.assertRaisesRegex(ValueError, "Symlink"):
            target.bound(self.root, "link", hashlib.sha256(b"frozen").hexdigest())

    def test_invalid_units(self):
        for units in ([0], [11], [1, 1], [1, -1], [True]):
            with self.subTest(units=units), self.assertRaises(ValueError):
                target.units_bytes(units, 10)

    def test_output_inside_snapshot(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            target.exclusive_output(self.root, self.root / "out", (b"cnf",))
        self.assertFalse((self.root / "out").exists())

    def test_formula_hash_rejected(self):
        obj = object.__new__(target.Family)
        obj.family = "A"
        prefix, suffix = b"p cnf 1 1\n", b"1 0\n"
        obj.ordinary_prefix = lambda _: ((prefix, hashlib.sha256(prefix)), suffix, "0" * 64, len(prefix) + len(suffix))
        with self.assertRaisesRegex(ValueError, "Complete formula hash/size"):
            obj.formula({"case_id": "synthetic"})

    def test_formula_size_rejected(self):
        obj = object.__new__(target.Family)
        obj.family = "A"
        prefix, suffix = b"p cnf 1 1\n", b"1 0\n"
        digest = hashlib.sha256(prefix + suffix).hexdigest()
        obj.ordinary_prefix = lambda _: ((prefix, hashlib.sha256(prefix)), suffix, digest, 1)
        with self.assertRaisesRegex(ValueError, "Complete formula hash/size"):
            obj.formula({"case_id": "synthetic"})

    def test_actual_shape_suffix_rejected(self):
        obj = object.__new__(target.Family)
        obj.family = "A"
        obj.cache = {"fixture": (b"p cnf 1 1\n", hashlib.sha256(b"p cnf 1 1\n"))}
        obj.manifest = {"prefixes": {"fixture": {"variables": 1, "clauses": 1, "base_clauses": 0}}}
        case = {"prefix_key": "fixture", "variables": 1, "clauses": 1, "dense_units": [1], "suffix_sha256": "0" * 64}
        with self.assertRaisesRegex(ValueError, "Suffix digest"):
            obj.ordinary_prefix(case)


if __name__ == "__main__":
    unittest.main(verbosity=2)
