# Eight lines in ℝ³ cannot have pairwise distance one

This computational companion replays the finite certificates used in the proof. The programs use exact integer arithmetic and the Python 3 standard library. The analytic geometry in the paper and completeness of the published 135-class oriented-matroid catalogue remain separate mathematical inputs.

The direction-sign rows are deliberately absent. Obtain the [uniform IC(8,3) catalogue page](https://finschi.com/math/om/?p=catom&card=8&rank=3&filter=nondeg) yourself and save its HTML or plain text locally, for example as `input/finschi.html`. The preparation script makes no network request.

Run:

```sh
python3 prepare_inputs.py input/finschi.html
python3 verify.py
python3 verify_metric_independent.py
python3 test_prepare_inputs.py --source input/finschi.html
```

`prepare_inputs.py` requires exactly the indexed rows 1 through 135, each with 56 signs. It hashes the canonical lines `index:signs\n` and accepts only SHA-256 `3873eece152716c6db5f8d254c1c29fa695f82c7d0c1f45b85350d4440c205af`, the value computed from the private reviewed input. It then reconstructs the former JSON layouts in the ignored `generated/` directory and expands the 135 unchanged proof-tree payloads from `proofs.zip`.

The distributed files are:

- `matching_masks.json`: the 1,027 original raw signed-distance masks, grouped by catalogue index.
- `metric_certificates.json`: the original normalized masks and five-label witnesses, plus each certificate's raw-mask provenance.
- `proofs.zip`: the 135 original binary exhaustion trees, with unchanged member bytes.
- `prepare_inputs.py`, `verify.py`, and `verify_metric_independent.py`: input reconstruction, complete finite replay, and an independent metric-certificate audit.
- `test_prepare_inputs.py`: rejects missing and changed source rows and checks reconstruction. Maintainers with the private reviewed companion can add `--private-companion PATH` to compare every reconstructed mathematical field and every tree byte.

A successful `verify.py` run reports 135 catalogue classes, 135 exhaustion trees, 153,080 exhaustion leaves, and 1,027 exact metric certificates. A successful independent audit reports exact coverage of all 1,027 input pairs. These checks do not prove the external catalogue classification or the paper's analytic lemmas, and they use no SAT solver, numerical optimizer, or third-party Python package.

See `NOTICE.md` for attribution and the precise license scope. The MIT license covers only the three original Python programs named there; it does not cover the certificate or data files.
