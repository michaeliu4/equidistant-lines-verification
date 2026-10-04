import Results.EightEquidistantLines.Solution.NoParallel

/-!
# Signed distances and the well-formedness of the sign data

* `T_sq` : unit distance means `T_{ij}² = ‖u_i × u_j‖²` for `i ≠ j` (paper, Section 2).
* `sd_wf` : the sign data is alternating / symmetric (all determinants and distances are non-zero).
-/

namespace Results.EightEquidistantLines

open V3

namespace Signs

/-- Negation flips the negativity flag of a non-zero real. -/
theorem flag_neg {x : ℝ} (hx : x ≠ 0) : decide (-x < 0) = !decide (x < 0) := by
  rcases lt_or_gt_of_ne hx with p | p
  · have : ¬ (-x < 0) := not_lt.2 (neg_nonneg.2 p.le)
    simp [p, this]
  · have : -x < 0 := neg_lt_zero.2 p
    simp [this, not_lt.2 p.le]

/-- A duplicate-free list of three labels yields the three pairwise inequalities. -/
theorem nodup3 {a b c : Fin 8} (h : [a, b, c].Nodup) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp [List.nodup_cons] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Signs

theorem UFam.T_sq (F : UFam) {i j : Fin 8} (h : i ≠ j) :
    F.T i j ^ 2 = norm2 (cross (F.u i) (F.u j)) := by
  have hc := F.cross_ne h
  have hN : 0 < norm2 (cross (F.u i) (F.u j)) :=
    lt_of_le_of_ne (norm2_nonneg _) (fun h0 => hc ((norm2_eq_zero_iff _).1 h0.symm))
  have hs : 0 < Real.sqrt (norm2 (cross (F.u i) (F.u j))) := Real.sqrt_pos.2 hN
  have h1 := F.dist1 i j h
  rw [lineDist3_skew _ _ _ _ hc, div_eq_one_iff_eq hs.ne'] at h1
  calc F.T i j ^ 2 = |F.T i j| ^ 2 := (sq_abs _).symm
    _ = norm2 (cross (F.u i) (F.u j)) := by rw [UFam.T, h1, Real.sq_sqrt hN.le]

theorem UFam.T_ne (F : UFam) {i j : Fin 8} (h : i ≠ j) : F.T i j ≠ 0 := by
  intro h0
  have h2 := F.T_sq h
  rw [h0] at h2
  have h3 : norm2 (cross (F.u i) (F.u j)) = 0 := by rw [← h2]; norm_num
  exact F.cross_ne h ((norm2_eq_zero_iff _).1 h3)

theorem UFam.sd_wf (F : UFam) : F.sd.Wf := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c h
    obtain ⟨hab, hac, hbc⟩ := Signs.nodup3 h
    have hne := F.det_ne hab hac hbc
    simp only [UFam.sd_neg3]
    rw [det_swap12 (F.u a) (F.u b) (F.u c)]
    exact Signs.flag_neg hne
  · intro a b c h
    obtain ⟨hab, hac, hbc⟩ := Signs.nodup3 h
    have hne := F.det_ne hab hac hbc
    simp only [UFam.sd_neg3]
    rw [det_swap23 (F.u a) (F.u b) (F.u c)]
    exact Signs.flag_neg hne
  · intro a b
    simp only [UFam.sd_neg2, F.T_symm a b]

end Results.EightEquidistantLines
