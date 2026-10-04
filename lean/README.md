# Lean proof of the upper bound

This standalone development proves two statements from *Eight lines in ℝ³
cannot have pairwise distance one*:

- `Results.EightEquidistantLines.thm_1_1`: no eight affine lines in ℝ³ have all pairwise distances equal to one.
- `Results.EightEquidistantLines.cor_1_2_upper`: for every `n ≥ 8` and `d > 0`, no `n` affine lines in ℝ³ have common pairwise distance `d`.

A line is an affine subspace with one-dimensional direction space. Its distance
from another line is the infimum of Euclidean point-to-point distances.
`Defs.lean` defines this Euclidean distance explicitly on `Fin 3 → ℝ`; the
function space's default sup metric is not used.

Seven-line existence, the cylinder reformulation, the catalogue classification
and the separate Python replay are outside this formal proof.

## Build

Lean 4.32.1 and Mathlib v4.32.1 are pinned. The Mathlib commit is
`520045ab14e26149ee970e2e617ca04b09bde5d6`. With elan installed, run from
this directory:

```sh
lake exe cache get
lake build
lake env lean PrintAxioms.lean
```

The first command retrieves Mathlib's compiled cache. The second builds the
complete development, including the literal finite certificates and definition
tests. The third prints the two statements and their axiom dependencies. Both
axiom lists should contain only `propext`, `Classical.choice` and `Quot.sound`.

A fresh kernel replay is available after building:

```sh
lake env leanchecker --fresh Results.EightEquidistantLines.Solution.Main
```

The replay includes the imported Mathlib closure and takes several minutes.
All supplied proof, definition and test files are complete. No placeholder
statement, additional axiom or compiled-evaluation shortcut is imported.
`verification.json` records the precise source hashes and check scope.

## Proof structure

The direction lemma follows the manuscript's coordinate argument.
`CoordinateFrame.lean` constructs orthonormal coordinates from a hypothetical
parallel pair. `CoordinateObstruction.lean` derives the two base-distance
identities and excludes the resulting plane and transverse-coordinate cases.
`CoordinateTriple.lean` excludes three nonparallel coplanar directions using
three scalar normal coordinates. `NoParallel.lean` combines these results. The direction lemmas are stated for
the eight-line family needed here; the paper's general formulation for at least
five lines is not a separate formalized statement.

The subsequent geometric modules associate sign data to a hypothetical family
of eight unit-distance lines. These data satisfy `Valid8`: well-formedness,
three-term Grassmann–Plücker relations, four-line circuit constraints and a
five-line obstruction. `KFinal.lean` proves `Kfinal.no_valid8` by complete
orderly generation. The literal representatives and certificates are in
`Solution/Kdata/` and `Solution/KCheck/`; the accompanying `K*.lean` modules
prove that this generation covers every admissible datum. The finite facts
use `decide +kernel`.

This finite route is self-contained and does not use Finschi's 135-class
catalogue. It does not certify the separate Python program's class or leaf
counts. No catalogue-derived direction-sign rows are supplied here.

## License

Lean and Mathlib retain their own licenses. The repository's existing MIT grant
applies only to the original Python files named in the root `NOTICE.md`.
No additional license grant is made for these Lean sources or literal
certificate data.
