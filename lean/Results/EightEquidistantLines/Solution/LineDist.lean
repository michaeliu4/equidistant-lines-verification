import Results.EightEquidistantLines.Solution.Vec

/-!
# Distance between two lines, in coordinates

`lineDist3 p u q v` is the infimum of `‖(p + s u) - (q + t v)‖` over the two line parameters `s, t`
(the paper's definition of the distance of the lines `p + ℝu` and `q + ℝv`).  `Bridge.lean` identifies
it with `setDist` of the corresponding affine subspaces of `E3 = Fin 3 → ℝ`.

* `lineDist3_skew` : skew-line distance formula `|det(p - q, u, v)| / ‖u × v‖` (paper, Section 2).
* `lineDist3_parallel` : distance of parallel lines, for a unit direction `u`.
-/

namespace Results.EightEquidistantLines

open V3

/-- Distance of the lines `p + ℝ u` and `q + ℝ v` (infimum over the line parameters). -/
noncomputable def lineDist3 (p u q v : V3) : ℝ :=
  sInf {r : ℝ | ∃ s t : ℝ, r = Real.sqrt (norm2 ((p - q) + s • u - t • v))}

namespace LineDist

/-- Cauchy-Schwarz in Lagrange form: `(z · n)² ≤ ‖z‖² ‖n‖²`. -/
theorem dot_sq_le (z n : V3) : dot z n ^ 2 ≤ norm2 z * norm2 n := by
  have h := norm2_nonneg (cross z n)
  rw [norm2_cross] at h
  linarith

/-- Moving along the two lines does not change the component along `u × v`. -/
theorem dot_comb (w u v : V3) (s t : ℝ) :
    dot (w + s • u - t • v) (cross u v) = dot w (cross u v) := by
  simp only [dot, cross_x, cross_y, cross_z, add_x, add_y, add_z, sub_x, sub_y, sub_z,
    smul_x, smul_y, smul_z]
  ring

/-- Cramer's rule in the basis `u, v, u × v`. -/
theorem cramer (u v m : V3) :
    norm2 (cross u v) • m = dot (cross m v) (cross u v) • u + dot (cross u m) (cross u v) • v
      + dot m (cross u v) • cross u v := by
  ext <;> simp only [norm2, dot, cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y,
    smul_z] <;> ring

/-- A vector orthogonal to `u × v` is a combination `s u - t v`. -/
theorem exists_st (u v m : V3) (hn : cross u v ≠ 0) (hm : dot m (cross u v) = 0) :
    ∃ s t : ℝ, m = s • u - t • v := by
  have hN : norm2 (cross u v) ≠ 0 := fun h => hn ((norm2_eq_zero_iff _).1 h)
  have h := cramer u v m
  rw [hm] at h
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp only [smul_x, smul_y, smul_z, add_x, add_y, add_z] at hx hy hz
  refine ⟨dot (cross m v) (cross u v) / norm2 (cross u v),
    -dot (cross u m) (cross u v) / norm2 (cross u v), ?_⟩
  ext
  · simp only [smul_x, sub_x]
    field_simp
    linarith
  · simp only [smul_y, sub_y]
    field_simp
    linarith
  · simp only [smul_z, sub_z]
    field_simp
    linarith

/-- The skew distance is the least value of the set defining `lineDist3`. -/
theorem skew_isLeast (w u v : V3) (h : cross u v ≠ 0) :
    IsLeast {r : ℝ | ∃ s t : ℝ, r = Real.sqrt (norm2 (w + s • u - t • v))}
      (|dot w (cross u v)| / Real.sqrt (norm2 (cross u v))) := by
  have hN : 0 < norm2 (cross u v) :=
    lt_of_le_of_ne (norm2_nonneg _) (fun h0 => h ((norm2_eq_zero_iff _).1 h0.symm))
  have hN' : norm2 (cross u v) ≠ 0 := hN.ne'
  have hR : 0 < Real.sqrt (norm2 (cross u v)) := Real.sqrt_pos.2 hN
  constructor
  · -- the value is attained at `w + s u - t v = (w·n / ‖n‖²) n`
    have hm : dot ((dot w (cross u v) / norm2 (cross u v)) • cross u v - w) (cross u v) = 0 := by
      rw [sub_dot, smul_dot]
      have e : dot (cross u v) (cross u v) = norm2 (cross u v) := rfl
      rw [e]
      field_simp
      ring
    obtain ⟨s, t, hst⟩ := exists_st u v _ h hm
    have hz : w + s • u - t • v = (dot w (cross u v) / norm2 (cross u v)) • cross u v := by
      ext
      · have h1 := congrArg V3.x hst
        simp only [smul_x, sub_x, add_x] at h1 ⊢
        linarith
      · have h1 := congrArg V3.y hst
        simp only [smul_y, sub_y, add_y] at h1 ⊢
        linarith
      · have h1 := congrArg V3.z hst
        simp only [smul_z, sub_z, add_z] at h1 ⊢
        linarith
    refine ⟨s, t, ?_⟩
    rw [hz, eq_comm]
    refine (Real.sqrt_eq_iff_mul_self_eq (norm2_nonneg _) (div_nonneg (abs_nonneg _) hR.le)).2 ?_
    have e1 : norm2 ((dot w (cross u v) / norm2 (cross u v)) • cross u v)
        = (dot w (cross u v) / norm2 (cross u v)) ^ 2 * norm2 (cross u v) := by
      simp only [norm2, dot, smul_x, smul_y, smul_z]; ring
    have hRR : Real.sqrt (norm2 (cross u v)) * Real.sqrt (norm2 (cross u v)) = norm2 (cross u v) :=
      Real.mul_self_sqrt hN.le
    have hdd : |dot w (cross u v)| * |dot w (cross u v)| = dot w (cross u v) * dot w (cross u v) :=
      abs_mul_abs_self _
    rw [e1, div_mul_div_comm, hdd, hRR]
    field_simp
  · -- lower bound via Cauchy-Schwarz
    rintro r ⟨s, t, rfl⟩
    rw [div_le_iff₀ hR]
    have h2 := dot_sq_le (w + s • u - t • v) (cross u v)
    rw [dot_comb] at h2
    calc |dot w (cross u v)|
        ≤ Real.sqrt (norm2 (w + s • u - t • v) * norm2 (cross u v)) := Real.abs_le_sqrt h2
      _ = Real.sqrt (norm2 (w + s • u - t • v)) * Real.sqrt (norm2 (cross u v)) :=
          Real.sqrt_mul (norm2_nonneg _) _

/-- A unit vector `u` with `u × v = 0` satisfies `v = (u · v) u`. -/
theorem par_eq (u v : V3) (hu : norm2 u = 1) (h : cross u v = 0) : v = dot u v • u := by
  have h1 : norm2 (cross u v) = 0 := by
    rw [h]; simp only [norm2, dot, zero_x, zero_y, zero_z]; ring
  rw [norm2_cross, hu] at h1
  have h2 : norm2 (v - dot u v • u) = 0 := by
    have e : norm2 (v - dot u v • u) = norm2 v - 2 * dot u v ^ 2 + dot u v ^ 2 * norm2 u := by
      simp only [norm2, dot, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z]; ring
    rw [e, hu]; linarith
  have h3 := (norm2_eq_zero_iff _).1 h2
  have hx := congrArg V3.x h3
  have hy := congrArg V3.y h3
  have hz := congrArg V3.z h3
  simp only [sub_x, sub_y, sub_z, smul_x, smul_y, smul_z, zero_x, zero_y, zero_z] at hx hy hz
  ext
  · simp only [smul_x]; linarith
  · simp only [smul_y]; linarith
  · simp only [smul_z]; linarith

/-- Expansion of the squared length along the parallel line `v = c u`. -/
theorem norm2_par (w u : V3) (s t c : ℝ) :
    norm2 (w + s • u - t • (c • u))
      = norm2 w + 2 * (s - t * c) * dot w u + (s - t * c) ^ 2 * norm2 u := by
  simp only [norm2, dot, add_x, add_y, add_z, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z]
  ring

/-- The parallel distance is the least value of the set defining `lineDist3`. -/
theorem par_isLeast (w u : V3) (c : ℝ) (hu : norm2 u = 1) :
    IsLeast {r : ℝ | ∃ s t : ℝ, r = Real.sqrt (norm2 (w + s • u - t • (c • u)))}
      (Real.sqrt (norm2 w - dot w u ^ 2)) := by
  constructor
  · refine ⟨-dot w u, 0, ?_⟩
    rw [norm2_par, hu]
    congr 1
    ring
  · rintro r ⟨s, t, rfl⟩
    apply Real.sqrt_le_sqrt
    rw [norm2_par, hu]
    nlinarith [sq_nonneg (s - t * c + dot w u)]

end LineDist

/-- Distance of two non-parallel lines (paper, Section 2): `|det(p - q, u, v)| / ‖u × v‖`. -/
theorem lineDist3_skew (p u q v : V3) (h : cross u v ≠ 0) :
    lineDist3 p u q v = |det (p - q) u v| / Real.sqrt (norm2 (cross u v)) := by
  exact (LineDist.skew_isLeast (p - q) u v h).csInf_eq

/-- Distance of two parallel lines (`v ≠ 0` parallel to the unit vector `u`):
`√(‖p - q‖² - ((p - q) · u)²)`. -/
theorem lineDist3_parallel (p u q v : V3) (hu : norm2 u = 1) (hv : v ≠ 0) (h : cross u v = 0) :
    lineDist3 p u q v = Real.sqrt (norm2 (p - q) - dot (p - q) u ^ 2) := by
  obtain ⟨c, rfl⟩ : ∃ c : ℝ, v = c • u := ⟨dot u v, LineDist.par_eq u v hu h⟩
  exact (LineDist.par_isLeast (p - q) u c hu).csInf_eq

end Results.EightEquidistantLines
