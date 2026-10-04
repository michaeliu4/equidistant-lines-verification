import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Eight lines in ℝ³: statement-level definitions

Paper: "Eight lines in R^3 cannot have pairwise distance one" (M. Liu), Theorem 1.1 and the upper half of
Corollary 1.2.

* `E3` is the coordinate space `ℝ³` (`Fin 3 → ℝ`), with its usual affine structure.
* `eucDist x y` is the Euclidean distance `√((x₀ - y₀)² + (x₁ - y₁)² + (x₂ - y₂)²)`.  It is written out
  explicitly, so that no norm or metric instance on `Fin 3 → ℝ` (Mathlib's default metric there is the
  sup metric) can enter the statements.  (Mathlib's `EuclideanSpace ℝ (Fin 3)` carries the same metric; that
  identification is proved in `statement-read/EquivDraftB.lean.txt`, outside the audited closure.  The
  coordinate form keeps the import closure of the statement layer small: the checks of the formal
  workflow replay that closure.)
* `IsAffineLine L` : `L` is an affine line, i.e. an affine subspace of `ℝ³` whose direction space has
  dimension `1` (this excludes the empty subspace, points, planes and `ℝ³` itself).
* `setDist A B` : the distance between two sets, `inf { eucDist x y : x ∈ A, y ∈ B }` (the paper's definition
  of the distance of two lines; for non-empty `A`, `B` the set is non-empty and bounded below by `0`).
-/

namespace Results.EightEquidistantLines

/-- Three-dimensional real coordinate space `ℝ³`. -/
abbrev E3 : Type := Fin 3 → ℝ

/-- The Euclidean distance of two points of `ℝ³`. -/
noncomputable def eucDist (x y : E3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (x i - y i) ^ 2)

/-- An affine line in `ℝ³`: an affine subspace with one-dimensional direction. -/
def IsAffineLine (L : AffineSubspace ℝ E3) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The distance between two sets of points of `ℝ³`: the infimum of the Euclidean distances between
their points. -/
noncomputable def setDist (A B : Set E3) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, eucDist x y = r}

end Results.EightEquidistantLines
