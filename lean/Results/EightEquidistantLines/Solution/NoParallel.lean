import Results.EightEquidistantLines.Solution.CoordinateFrame
import Results.EightEquidistantLines.Solution.CoordinateObstruction
import Results.EightEquidistantLines.Solution.CoordinateTriple

/-!
# Direction independence by the manuscript's coordinate proof

A hypothetical parallel pair supplies an orthonormal frame. The two base-distance
identities and the transverse-coordinate cases exclude such a pair. Three
nonparallel coplanar directions are excluded by their scalar normal coordinates.
The downstream direction-independence interfaces are unchanged.
-/

namespace Results.EightEquidistantLines

open V3

/-- No two directions in an eight-line unit-distance family are parallel. -/
theorem UFam.cross_ne (F : UFam) {i j : Fin 8} (h : i ≠ j) :
    cross (F.u i) (F.u j) ≠ 0 := by
  intro hpar
  obtain ⟨G, hpa, hua, hby, hbz, hcross⟩ :=
    F.exists_parallel_normalization i j h hpar
  exact CoordinateObstruction.normalized_false G i j h hpa hua hby hbz hcross

/-- Every three directions in an eight-line unit-distance family are independent. -/
theorem UFam.det_ne (F : UFam) {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    det (F.u i) (F.u j) (F.u k) ≠ 0 := by
  intro hdet
  exact coordinate_triple_false F hij hik hjk
    (F.cross_ne hij) (F.cross_ne hik) (F.cross_ne hjk) hdet

end Results.EightEquidistantLines
