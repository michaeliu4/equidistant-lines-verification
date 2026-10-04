import Results.EightEquidistantLines.Defs

/-!
# Scaling and restriction (upper half of Corollary 1.2)

`n ≥ 8` affine lines at a common positive pairwise distance `d` give, by restricting to the first
eight lines and scaling by `1/d`, eight affine lines at pairwise distance one.

The scaling is the dilation `x ↦ c • x` (centre `0`) of `ℝ³ = Fin 3 → ℝ`.  The image `c • L` of an
affine subspace `L` is again an affine subspace (`Scaling.dilSub`).  For `c ≠ 0` it has the same
direction space as `L`, so it is a line when `L` is; for `c ≥ 0` the dilation multiplies the
Euclidean distance `eucDist`, hence `setDist`, by `c`.

(`AffineMap` and `AffineSubspace.map` lie outside the small import closure of the statement layer,
so the image subspace is built directly from the pointwise image `c • (L : Set E3)`.)
-/

namespace Results.EightEquidistantLines

namespace Scaling

open scoped Pointwise

/-- The dilation `x ↦ c • x` multiplies the Euclidean distance by `c ≥ 0`. -/
theorem eucDist_smul (c : ℝ) (hc : 0 ≤ c) (x y : E3) :
    eucDist (c • x) (c • y) = c * eucDist x y := by
  unfold eucDist
  have h : ∑ i : Fin 3, ((c • x) i - (c • y) i) ^ 2 = c ^ 2 * ∑ i : Fin 3, (x i - y i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The distance between two sets of `ℝ³` is multiplied by `c ≥ 0` under the dilation by `c`. -/
theorem setDist_smul (c : ℝ) (hc : 0 ≤ c) (A B : Set E3) :
    setDist (c • A) (c • B) = c * setDist A B := by
  have key : {r : ℝ | ∃ x ∈ c • A, ∃ y ∈ c • B, eucDist x y = r}
      = c • {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, eucDist x y = r} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨eucDist x y, ⟨x, hx, y, hy, rfl⟩, (eucDist_smul c hc x y).symm⟩
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨c • x, ⟨x, hx, rfl⟩, c • y, ⟨y, hy, rfl⟩, eucDist_smul c hc x y⟩
  unfold setDist
  rw [key, Real.sInf_smul_of_nonneg hc, smul_eq_mul]

/-- The image `c • L` of an affine subspace `L` of `ℝ³` under the dilation `x ↦ c • x`. -/
def dilSub (c : ℝ) (L : AffineSubspace ℝ E3) : AffineSubspace ℝ E3 where
  carrier := c • (L : Set E3)
  smul_vsub_vadd_mem' t _ _ _ hp₁ hp₂ hp₃ := by
    obtain ⟨y₁, hy₁, rfl⟩ := Set.mem_smul_set.1 hp₁
    obtain ⟨y₂, hy₂, rfl⟩ := Set.mem_smul_set.1 hp₂
    obtain ⟨y₃, hy₃, rfl⟩ := Set.mem_smul_set.1 hp₃
    refine Set.mem_smul_set.2 ⟨t • (y₁ -ᵥ y₂) +ᵥ y₃, L.smul_vsub_vadd_mem t hy₁ hy₂ hy₃, ?_⟩
    funext i
    simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem coe_dilSub (c : ℝ) (L : AffineSubspace ℝ E3) :
    (dilSub c L : Set E3) = c • (L : Set E3) :=
  rfl

theorem smul_mem_dilSub (c : ℝ) {L : AffineSubspace ℝ E3} {p : E3} (hp : p ∈ L) :
    c • p ∈ dilSub c L := by
  rw [← SetLike.mem_coe, coe_dilSub]
  exact Set.smul_mem_smul_set hp

/-- For `c ≠ 0` the dilated subspace has the same direction space as the original one. -/
theorem direction_dilSub (c : ℝ) (hc : c ≠ 0) (L : AffineSubspace ℝ E3) :
    (dilSub c L).direction = L.direction := by
  apply le_antisymm
  · rw [AffineSubspace.direction_eq_vectorSpan (dilSub c L), vectorSpan_def, Submodule.span_le]
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_vsub.1 hv
    rw [coe_dilSub] at ha hb
    obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.1 ha
    obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.1 hb
    have h : c • p -ᵥ c • q = c • (p -ᵥ q) := by
      rw [vsub_eq_sub, vsub_eq_sub, smul_sub]
    rw [SetLike.mem_coe, h]
    exact L.direction.smul_mem c (AffineSubspace.vsub_mem_direction hp hq)
  · rw [AffineSubspace.direction_eq_vectorSpan L, vectorSpan_def, Submodule.span_le]
    intro v hv
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.1 hv
    have h : p -ᵥ q = c⁻¹ • (c • p -ᵥ c • q) := by
      rw [vsub_eq_sub, vsub_eq_sub, ← smul_sub, inv_smul_smul₀ hc]
    rw [SetLike.mem_coe, h]
    exact (dilSub c L).direction.smul_mem c⁻¹
      (AffineSubspace.vsub_mem_direction (smul_mem_dilSub c hp) (smul_mem_dilSub c hq))

/-- A dilation by a non-zero factor maps an affine line to an affine line. -/
theorem isAffineLine_dilSub (c : ℝ) (hc : c ≠ 0) (L : AffineSubspace ℝ E3)
    (hL : IsAffineLine L) : IsAffineLine (dilSub c L) := by
  unfold IsAffineLine at hL ⊢
  rw [direction_dilSub c hc]
  exact hL

/-- The distance between two affine subspaces is multiplied by `c ≥ 0` under the dilation by
`c`. -/
theorem setDist_dilSub (c : ℝ) (hc : 0 ≤ c) (A B : AffineSubspace ℝ E3) :
    setDist (dilSub c A) (dilSub c B) = c * setDist A B := by
  rw [coe_dilSub, coe_dilSub]
  exact setDist_smul c hc A B

end Scaling

theorem scale_lines (n : ℕ) (hn : 8 ≤ n) (d : ℝ) (hd : 0 < d) (L : Fin n → AffineSubspace ℝ E3)
    (hL : ∀ i, IsAffineLine (L i)) (hdist : ∀ i j, i < j → setDist (L i) (L j) = d) :
    ∃ L' : Fin 8 → AffineSubspace ℝ E3,
      (∀ i, IsAffineLine (L' i)) ∧ ∀ i j, i < j → setDist (L' i) (L' j) = 1 := by
  have hc : (0 : ℝ) < d⁻¹ := inv_pos.2 hd
  refine ⟨fun i => Scaling.dilSub d⁻¹ (L (Fin.castLE hn i)), fun i => ?_, fun i j hij => ?_⟩
  · exact Scaling.isAffineLine_dilSub _ hc.ne' _ (hL _)
  · rw [Scaling.setDist_dilSub _ hc.le, hdist _ _ ((Fin.castLE_lt_castLE_iff hn).2 hij),
      inv_mul_cancel₀ hd.ne']

end Results.EightEquidistantLines
