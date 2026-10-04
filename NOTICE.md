# Source attribution and license scope

The MIT license applies only to the original code in these files:

- `prepare_inputs.py`
- `verify.py`
- `verify_metric_independent.py`

The certificate material and data in `matching_masks.json`, `metric_certificates.json`, and `proofs.zip` are excluded from that license grant. No license for those files is granted by this repository.

The direction-sign data required at run time come from L. Finschi's *Catalogue of Oriented Matroids*, [uniform IC(8,3), 135 classes](https://finschi.com/math/om/?p=catom&card=8&rank=3&filter=nondeg), accessed 30 September 2026. The catalogue rows are not included in this repository. A user must obtain and save the source page separately; `prepare_inputs.py` authenticates the extracted rows and reconstructs local, ignored run-time inputs.

Separate permission to redistribute the catalogue-derived direction-sign arrays has not been obtained. The MIT license for the listed code does not grant rights to the catalogue material, the excluded certificate files, or the generated run-time data, and this notice supplies no new data-license grant.

The Lean sources and literal certificate data added in `lean/` are also outside the existing MIT grant. No additional license is granted for them. Lean and Mathlib are external dependencies governed by their own licenses; no Mathlib sources are vendored in this repository. See `lean/README.md` for the formal proof's scope and source attribution.
