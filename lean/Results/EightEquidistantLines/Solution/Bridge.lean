import Results.EightEquidistantLines.Defs
import Results.EightEquidistantLines.Solution.Family

/-!
# From affine lines in the coordinate space `ℝ³` to a unit-distance family

`E3 = Fin 3 → ℝ`.  An affine line `L` (an affine subspace with one-dimensional direction) can be
written `p + ℝ u` with a unit vector `u` (`u₀² + u₁² + u₂² = 1`); `setDist` of two such lines (an
infimum of the explicit Euclidean distances `eucDist`) is `lineDist3` of the coordinate data.  Hence
eight affine lines at pairwise `setDist` one give a `UFam`.  Only the coordinate formula `eucDist`
is used, never Mathlib's (sup) norm or metric on `Fin 3 → ℝ`.
-/

namespace Results.EightEquidistantLines

open V3

/-- Coordinates of a point of `ℝ³`. -/
noncomputable def toV3 (x : E3) : V3 := ⟨x 0, x 1, x 2⟩

namespace Bridge

/-- A one-dimensional subspace of `ℝ³` is spanned by one nonzero vector.  (Derived from
`Module.le_rank_iff`: a linearly independent pair would give rank at least two.) -/
theorem exists_dir (W : Submodule ℝ E3) (h : Module.finrank ℝ W = 1) :
    ∃ v : E3, v ∈ W ∧ v ≠ 0 ∧ ∀ w ∈ W, ∃ c : ℝ, w = c • v := by
  have hr : Module.rank ℝ W = 1 := Module.rank_eq_one_iff_finrank_eq_one.2 h
  obtain ⟨f, hf⟩ := (Module.le_rank_iff (R := ℝ) (M := W) (n := 1)).1 (by rw [hr]; norm_num)
  have hf0 : (f 0 : E3) ≠ 0 := fun h0 => hf.ne_zero 0 (Subtype.ext h0)
  refine ⟨f 0, (f 0).2, hf0, fun w hw => by_contra fun hne => ?_⟩
  -- otherwise `f 0, w` would be linearly independent in `W`
  have hli : LinearIndependent ℝ (![f 0, ⟨w, hw⟩] : Fin 2 → W) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 := congrArg Subtype.val hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] at h2
    have hg1 : g 1 = 0 := by
      rcases eq_or_ne (g 1) 0 with h1 | h1
      · exact h1
      · refine absurd ⟨-(g 0) / g 1, ?_⟩ hne
        funext i
        have := congrFun h2 i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        field_simp
        linarith
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_smul, add_zero] at h2
      rcases eq_or_ne (g 0) 0 with h0 | h0
      · exact h0
      · refine absurd ?_ hf0
        funext i
        have := congrFun h2 i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h h0
        · exact h
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  have h2 := (Module.le_rank_iff (R := ℝ) (M := W) (n := 2)).2 ⟨_, hli⟩
  rw [hr] at h2
  norm_num at h2

/-- A point with vanishing coordinates is `0`. -/
theorem toV3_eq_zero {w : E3} (h : toV3 w = 0) : w = 0 := by
  have h0 := congrArg V3.x h
  have h1 := congrArg V3.y h
  have h2 := congrArg V3.z h
  simp only [toV3, zero_x, zero_y, zero_z] at h0 h1 h2
  funext i
  fin_cases i <;> simp [h0, h1, h2]

/-- An affine line (one-dimensional direction) is `p + ℝ u` with a unit vector `u`, i.e.
`u₀² + u₁² + u₂² = 1`. -/
theorem exists_param (L : AffineSubspace ℝ E3) (hL : IsAffineLine L) :
    ∃ p u : E3, norm2 (toV3 u) = 1 ∧ ∀ x : E3, x ∈ L ↔ ∃ t : ℝ, x = p + t • u := by
  obtain ⟨v, hvL, hv0, hspan⟩ := exists_dir L.direction hL
  have hne : (L : Set E3).Nonempty := by
    rw [AffineSubspace.nonempty_iff_ne_bot]
    rintro rfl
    rw [AffineSubspace.direction_bot, Submodule.mem_bot] at hvL
    exact hv0 hvL
  obtain ⟨x₀, hx₀⟩ := hne
  have hN : 0 < norm2 (toV3 v) :=
    lt_of_le_of_ne (norm2_nonneg _) fun h => hv0 (toV3_eq_zero ((norm2_eq_zero_iff _).1 h.symm))
  have hc : (Real.sqrt (norm2 (toV3 v)))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 hN)
  refine ⟨x₀, (Real.sqrt (norm2 (toV3 v)))⁻¹ • v, ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have e : norm2 (toV3 ((Real.sqrt (norm2 (toV3 v)))⁻¹ • v))
        = ((Real.sqrt (norm2 (toV3 v)))⁻¹) ^ 2 * norm2 (toV3 v) := by
      simp only [norm2, dot, toV3, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']
  · obtain ⟨a, ha⟩ := hspan (x -ᵥ x₀) (AffineSubspace.vsub_mem_direction hx hx₀)
    refine ⟨a / (Real.sqrt (norm2 (toV3 v)))⁻¹, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hc, ← ha, vsub_eq_sub]
    abel
  · rintro ⟨t, rfl⟩
    have h := AffineSubspace.vadd_mem_of_mem_direction
      (L.direction.smul_mem (t * (Real.sqrt (norm2 (toV3 v)))⁻¹) hvL) hx₀
    rwa [vadd_eq_add, ← smul_smul, add_comm] at h

/-- The Euclidean distance between two points of two parametrised lines, in coordinates. -/
theorem eucDist_param (p u q v : E3) (t s : ℝ) :
    eucDist (p + t • u) (q + s • v) =
      Real.sqrt (norm2 ((toV3 p - toV3 q) + t • toV3 u - s • toV3 v)) := by
  unfold eucDist
  congr 1
  simp only [Fin.sum_univ_three, norm2, dot, toV3, sub_x, sub_y, sub_z, add_x, add_y, add_z,
    smul_x, smul_y, smul_z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `setDist` of two parametrised lines is `lineDist3` of their coordinate data. -/
theorem setDist_param (A B : Set E3) (p u q v : E3)
    (hA : ∀ x, x ∈ A ↔ ∃ t : ℝ, x = p + t • u) (hB : ∀ y, y ∈ B ↔ ∃ s : ℝ, y = q + s • v) :
    setDist A B = lineDist3 (toV3 p) (toV3 u) (toV3 q) (toV3 v) := by
  unfold setDist lineDist3
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (hA x).1 hx
    obtain ⟨s, rfl⟩ := (hB y).1 hy
    exact ⟨t, s, eucDist_param p u q v t s⟩
  · rintro ⟨t, s, rfl⟩
    exact ⟨p + t • u, (hA _).2 ⟨t, rfl⟩, q + s • v, (hB _).2 ⟨s, rfl⟩, eucDist_param p u q v t s⟩

/-- The Euclidean distance is symmetric. -/
theorem eucDist_comm (x y : E3) : eucDist x y = eucDist y x := by
  unfold eucDist
  congr 1
  simp only [Fin.sum_univ_three]
  ring

/-- `setDist` is symmetric. -/
theorem setDist_comm (A B : Set E3) : setDist A B = setDist B A := by
  unfold setDist
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, eucDist_comm y x⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, eucDist_comm y x⟩

end Bridge

/-- Eight affine lines of `ℝ³` at pairwise `setDist` one give a unit-distance family `UFam`. -/
theorem exists_ufam (L : Fin 8 → AffineSubspace ℝ E3) (hL : ∀ i, IsAffineLine (L i))
    (hd : ∀ i j, i < j → setDist (L i) (L j) = 1) : Nonempty UFam := by
  choose p u hu hmem using fun i => Bridge.exists_param (L i) (hL i)
  have hdist : ∀ i j, i ≠ j →
      lineDist3 (toV3 (p i)) (toV3 (u i)) (toV3 (p j)) (toV3 (u j)) = 1 := by
    intro i j hij
    rw [← Bridge.setDist_param (L i) (L j) (p i) (u i) (p j) (u j) (hmem i) (hmem j)]
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd i j h
    · rw [Bridge.setDist_comm]
      exact hd j i h
  exact ⟨{ p := fun i => toV3 (p i), u := fun i => toV3 (u i), unit := hu, dist1 := hdist }⟩

end Results.EightEquidistantLines
