"""Tests for reconstructing verifier inputs from a separately saved catalogue page."""

import argparse
import json
from pathlib import Path
import tempfile
import unittest

import prepare_inputs


PARSER = argparse.ArgumentParser(add_help=False)
PARSER.add_argument("--source", required=True, type=Path)
PARSER.add_argument("--private-companion", type=Path)
ARGS, UNITTEST_ARGS = PARSER.parse_known_args()


class PrepareInputsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source_text = ARGS.source.read_text(encoding="utf-8")

    def test_malformed_source_missing_row_fails(self):
        first_sign_row = prepare_inputs.extract_rows(self.source_text)[0][1]
        damaged = self.source_text.replace(first_sign_row, "not-a-sign-row", 1)
        with self.assertRaisesRegex(ValueError, "135 catalogue rows"):
            prepare_inputs.parse_catalogue(damaged)

    def test_changed_sign_row_fails_digest(self):
        rows = prepare_inputs.extract_rows(self.source_text)
        old = rows[0][1]
        changed = ("-" if old[0] == "+" else "+") + old[1:]
        damaged = self.source_text.replace(old, changed, 1)
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            prepare_inputs.parse_catalogue(damaged)

    def test_reconstruction_and_direction_data_separation(self):
        package = Path(__file__).resolve().parent
        for name in ("matching_masks.json", "metric_certificates.json"):
            value = json.loads((package / name).read_text(encoding="utf-8"))
            encoded = (package / name).read_text(encoding="utf-8")
            self.assertNotIn("revlex_chirotope", encoded)

            def visit(node):
                if isinstance(node, dict):
                    self.assertNotIn("chi", node)
                    for child in node.values():
                        visit(child)
                elif isinstance(node, list):
                    self.assertFalse(len(node) == 56 and set(node) <= {-1, 1})
                    for child in node:
                        visit(child)

            visit(value)

        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "generated"
            prepare_inputs.prepare(ARGS.source, output, package)
            catalogue = json.loads((output / "data/catalogue.json").read_text())
            matching = json.loads((output / "data/matching_pairs.json").read_text())
            certificates = json.loads((output / "data/certificates.json").read_text())
            self.assertEqual([r["index"] for r in catalogue["representatives"]], list(range(1, 136)))
            self.assertEqual(len(matching["representatives"]), 135)
            self.assertEqual(sum(r["epsilon_count"] for r in matching["representatives"]), 1027)
            self.assertEqual(len(certificates), 1027)
            self.assertEqual(len(list((output / "proofs").glob("chi_*.tree"))), 135)

            if ARGS.private_companion:
                private = ARGS.private_companion
                for name in ("catalogue.json", "matching_pairs.json", "certificates.json"):
                    expected = json.loads((private / "data" / name).read_text())
                    actual = json.loads((output / "data" / name).read_text())
                    self.assertEqual(actual, expected, name)
                for index in range(1, 136):
                    name = f"chi_{index:03d}.tree"
                    self.assertEqual(
                        (output / "proofs" / name).read_bytes(),
                        (private / "proofs" / name).read_bytes(),
                        name,
                    )


if __name__ == "__main__":
    unittest.main(argv=[__file__, *UNITTEST_ARGS])
