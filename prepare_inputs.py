"""Reconstruct verifier inputs from a separately saved Finschi catalogue page.

This program performs no network access. It accepts HTML or plain text saved
from the source URL documented in README.md, authenticates the extracted 135
sign rows, and combines them with this package's original finite certificates.
"""

import argparse
import hashlib
import html
import itertools
import json
from pathlib import Path
import re
import shutil
import tempfile
import zipfile


SOURCE_URL = "https://finschi.com/math/om/?p=catom&card=8&rank=3&filter=nondeg"
EXPECTED_ROWS_SHA256 = "3873eece152716c6db5f8d254c1c29fa695f82c7d0c1f45b85350d4440c205af"
ROW_PATTERN = re.compile(
    r"IC\s*\(\s*8\s*,\s*3\s*,\s*(\d+)\s*\)\s*=\s*([+-]+)",
    re.IGNORECASE,
)
TRIPLES = list(itertools.combinations(range(8), 3))
COLEX_TRIPLES = sorted(TRIPLES, key=lambda triple: triple[::-1])
PAIRS = list(itertools.combinations(range(8), 2))
NORMALIZED_PAIRS = list(itertools.combinations(range(1, 8), 2))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def extract_rows(source_text):
    """Return all IC(8,3,index) sign rows found in HTML or plain text."""
    decoded = html.unescape(source_text)
    return [(int(index), signs) for index, signs in ROW_PATTERN.findall(decoded)]


def canonical_rows_bytes(rows):
    """Encode rows as one ``index:signs`` line each, including final newline."""
    return "".join(f"{index}:{signs}\n" for index, signs in rows).encode("ascii")


def parse_catalogue(source_text):
    rows = extract_rows(source_text)
    require(len(rows) == 135, f"Expected 135 catalogue rows, found {len(rows)}")
    require(
        [index for index, _ in rows] == list(range(1, 136)),
        "Catalogue indices must occur exactly once in the order 1 through 135",
    )
    bad_lengths = [index for index, signs in rows if len(signs) != 56]
    require(not bad_lengths, f"Each catalogue row must contain 56 signs; bad indices: {bad_lengths}")
    digest = hashlib.sha256(canonical_rows_bytes(rows)).hexdigest()
    require(
        digest == EXPECTED_ROWS_SHA256,
        f"Catalogue sign-row SHA-256 mismatch: expected {EXPECTED_ROWS_SHA256}, got {digest}",
    )
    return rows


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def catalogue_chi(signs):
    colex_values = dict(zip(COLEX_TRIPLES, (1 if sign == "+" else -1 for sign in signs)))
    return [colex_values[triple] for triple in TRIPLES]


def normalize_pair(raw_mask, chi):
    epsilon = {
        edge: 1 - 2 * ((raw_mask >> bit) & 1)
        for bit, edge in enumerate(PAIRS)
    }
    switch = [1] + [epsilon[0, vertex] for vertex in range(1, 8)]
    normalized_mask = sum(
        (epsilon[a, b] * switch[a] * switch[b] < 0) << bit
        for bit, (a, b) in enumerate(NORMALIZED_PAIRS)
    )
    normalized_chi = [
        value * switch[a] * switch[b] * switch[c]
        for value, (a, b, c) in zip(chi, TRIPLES)
    ]
    return normalized_mask, normalized_chi


def validate_matching_masks(compact):
    require(compact.get("source_url") == SOURCE_URL, "Unexpected matching-mask source URL")
    require(
        compact.get("ordering") == "lexicographic triples, zero-based labels",
        "Unexpected matching-mask ordering",
    )
    records = compact.get("representatives")
    require(isinstance(records, list) and len(records) == 135, "Expected 135 matching-mask records")
    require(
        [record.get("catalog_index") for record in records] == list(range(1, 136)),
        "Matching-mask indices must be exactly 1 through 135",
    )
    for record in records:
        masks = record.get("epsilon_masks")
        require(isinstance(masks, list), "epsilon_masks must be a list")
        require(record.get("epsilon_count") == len(masks), "epsilon_count does not match epsilon_masks")
        require(len(masks) == len(set(masks)), "epsilon_masks contains a duplicate")
        require(
            all(isinstance(mask, int) and 0 <= mask < (1 << 28) and mask & 1 == 0 for mask in masks),
            "Each raw mask must be a 28-bit integer with bit zero fixed to zero",
        )
    require(sum(record["epsilon_count"] for record in records) == 1027, "Expected 1027 raw masks")
    return records


def reconstruct(rows, package_dir):
    matching_compact = load_json(package_dir / "matching_masks.json")
    matching_records = validate_matching_masks(matching_compact)
    compact_certificates = load_json(package_dir / "metric_certificates.json")
    require(
        isinstance(compact_certificates, list) and len(compact_certificates) == 1027,
        "Expected 1027 compact metric certificates",
    )

    chi_by_index = {index: catalogue_chi(signs) for index, signs in rows}
    raw_pairs = {
        (record["catalog_index"], raw_mask)
        for record in matching_records
        for raw_mask in record["epsilon_masks"]
    }
    certificate_pairs = [
        (record.get("catalog_index"), record.get("raw_mask"))
        for record in compact_certificates
    ]
    require(len(set(certificate_pairs)) == 1027, "Certificate raw-mask provenance must be unique")
    require(set(certificate_pairs) == raw_pairs, "Certificate raw-mask provenance must cover every raw mask")

    catalogue = {
        "source_url": SOURCE_URL,
        "status": "Published catalogue, completeness not independently replayed",
        "representatives": [
            {"index": index, "revlex_chirotope": signs} for index, signs in rows
        ],
    }
    matching = {
        "source_url": matching_compact["source_url"],
        "ordering": matching_compact["ordering"],
        "representatives": [
            {
                "catalog_index": record["catalog_index"],
                "chi": chi_by_index[record["catalog_index"]],
                "epsilon_masks": record["epsilon_masks"],
                "epsilon_count": record["epsilon_count"],
            }
            for record in matching_records
        ],
    }

    certificates = []
    for compact in compact_certificates:
        require(
            set(compact) == {"catalog_index", "raw_mask", "mask", "certificates"},
            "Unexpected compact certificate fields",
        )
        index = compact["catalog_index"]
        raw_mask = compact["raw_mask"]
        require(index in chi_by_index, "Certificate has an invalid catalogue index")
        normalized_mask, normalized_chi = normalize_pair(raw_mask, chi_by_index[index])
        require(normalized_mask == compact["mask"], "Certificate normalized mask does not match provenance")
        witnesses = compact["certificates"]
        require(isinstance(witnesses, list) and len(witnesses) == 1, "Expected one witness per certificate")
        certificates.append(
            {
                "catalog_index": index,
                "mask": compact["mask"],
                "chi": normalized_chi,
                "certificates": witnesses,
            }
        )
    return catalogue, matching, certificates


def extract_proofs(archive_path, output_dir):
    expected = [f"chi_{index:03d}.tree" for index in range(1, 136)]
    with zipfile.ZipFile(archive_path) as archive:
        require(archive.namelist() == expected, "proofs.zip must contain exactly chi_001.tree through chi_135.tree")
        output_dir.mkdir(parents=True)
        for name in expected:
            data = archive.read(name)
            require(data, f"Proof tree {name} is empty")
            (output_dir / name).write_bytes(data)


def prepare(source_path, output_dir, package_dir=None):
    package_dir = Path(package_dir or Path(__file__).resolve().parent).resolve()
    source_path = Path(source_path)
    output_dir = Path(output_dir).resolve()
    require(output_dir.name == "generated", "The runtime output directory must be named generated")
    require(output_dir != package_dir, "Refusing to replace the package directory")
    rows = parse_catalogue(source_path.read_text(encoding="utf-8"))
    catalogue, matching, certificates = reconstruct(rows, package_dir)

    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="prepare-inputs-", dir=output_dir.parent) as temporary:
        staged = Path(temporary) / "generated"
        data_dir = staged / "data"
        data_dir.mkdir(parents=True)
        write_json(data_dir / "catalogue.json", catalogue)
        write_json(data_dir / "matching_pairs.json", matching)
        write_json(data_dir / "certificates.json", certificates)
        extract_proofs(package_dir / "proofs.zip", staged / "proofs")
        if output_dir.exists():
            shutil.rmtree(output_dir)
        shutil.copytree(staged, output_dir)
    return {
        "catalogue_classes": len(catalogue["representatives"]),
        "raw_matching_pairs": sum(r["epsilon_count"] for r in matching["representatives"]),
        "metric_certificates": len(certificates),
        "proof_trees": 135,
        "catalogue_rows_sha256": EXPECTED_ROWS_SHA256,
        "output": str(output_dir.resolve()),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="saved HTML or text from the documented Finschi catalogue URL")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent / "generated",
        help="runtime directory to replace (default: ./generated)",
    )
    args = parser.parse_args()
    print(json.dumps(prepare(args.source, args.output), indent=2))


if __name__ == "__main__":
    main()
