import Results.EightEquidistantLines.Solution.Signs

/-!
# Lemma 3.1: the four-line circuit condition

Paper, Section 3.  For four distinct labels `(v₀,v₁,v₂,v₃)`, with `α_k = (-1)^k det(.., omit k, ..)`,
`x_k = α_k u_{v_k}` satisfy `Σ x_k = 0`, hence `Σ_{i<j} α_i α_j T_{v_i v_j} = 0`, i.e.
`Σ σ_{ij} ‖x_i × x_j‖ = 0`; at each vertex the three vectors `x_i × x_j` sum to zero and are pairwise
non-parallel, so their lengths satisfy strict triangle inequalities, and neither sign class of `σ` is
a matching.

Organisation of the proof (helpers in namespace `Circuit`):
* `key_bool` : the purely real/Boolean core (six positive weights with twelve strict triangle
  inequalities, signed sum zero, then no sign class is a matching), by case analysis on the flags;
* `key_t` : the same with the weights `|t_ij|` and flags `decide (t_ij < 0)`;
* `circ_sum` : `Σ_{i<j} α_i α_j T_{ij} = 0` from `Σ α_k u_k = 0` (`T = Uᵀ M + Mᵀ U`, `m = p × u`);
* `vtx` : the three strict triangle inequalities at one vertex;
* `circ_core` : assembly for arbitrary vectors; `UFam.sd_circ` : instantiation.
-/

namespace Results.EightEquidistantLines

open V3

namespace Circuit

/-! ### Sign flags -/

theorem flag_neg {a : ℝ} (ha : a ≠ 0) : decide (-a < 0) = !decide (a < 0) := by
  rcases ha.lt_or_gt with h | h
  · rw [decide_eq_false (not_lt.mpr (neg_pos.mpr h).le), decide_eq_true h]; rfl
  · rw [decide_eq_true (neg_neg_of_pos h), decide_eq_false (not_lt.mpr h.le)]; rfl

theorem flag_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    decide (a * b < 0) = (decide (a < 0) ^^ decide (b < 0)) := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · rw [decide_eq_false (not_lt.mpr (mul_pos_of_neg_of_neg ha hb).le), decide_eq_true ha,
      decide_eq_true hb]; rfl
  · rw [decide_eq_true (mul_neg_of_neg_of_pos ha hb), decide_eq_true ha,
      decide_eq_false (not_lt.mpr hb.le)]; rfl
  · rw [decide_eq_true (mul_neg_of_pos_of_neg ha hb), decide_eq_false (not_lt.mpr ha.le),
      decide_eq_true hb]; rfl
  · rw [decide_eq_false (not_lt.mpr (mul_pos ha hb).le), decide_eq_false (not_lt.mpr ha.le),
      decide_eq_false (not_lt.mpr hb.le)]; rfl

theorem flag3 {T a b : ℝ} (hT : T ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (decide (T < 0) ^^ decide (a < 0) ^^ decide (b < 0)) = decide (a * b * T < 0) := by
  rw [flag_mul (mul_ne_zero ha hb) hT, flag_mul ha hb]
  cases decide (T < 0) <;> cases decide (a < 0) <;> cases decide (b < 0) <;> rfl

theorem ite_abs (t : ℝ) : (if decide (t < 0) then -|t| else |t|) = t := by
  by_cases h : t < 0
  · rw [decide_eq_true h, if_pos rfl, abs_of_neg h, neg_neg]
  · rw [decide_eq_false h, if_neg Bool.false_ne_true, abs_of_nonneg (not_lt.mp h)]

/-! ### The real/Boolean core -/

/-- Six weights satisfying the twelve strict triangle inequalities of `K₄` (edge `ij` is shorter
than the two other edges at `i`, and at `j`), whose signed sum vanishes: then for each colour `c`
some vertex carries two incident edges of colour `c` (no sign class is a matching). -/
theorem key_bool (w01 w02 w03 w12 w13 w23 : ℝ) (f01 f02 f03 f12 f13 f23 : Bool)
    (h0a : w01 < w02 + w03) (h0b : w02 < w01 + w03) (h0c : w03 < w01 + w02)
    (h1a : w01 < w12 + w13) (h1b : w12 < w01 + w13) (h1c : w13 < w01 + w12)
    (h2a : w02 < w12 + w23) (h2b : w12 < w02 + w23) (h2c : w23 < w02 + w12)
    (h3a : w03 < w13 + w23) (h3b : w13 < w03 + w23) (h3c : w23 < w03 + w13)
    (hsum : (if f01 then -w01 else w01) + (if f02 then -w02 else w02) + (if f03 then -w03 else w03)
      + (if f12 then -w12 else w12) + (if f13 then -w13 else w13) + (if f23 then -w23 else w23) = 0)
    (c : Bool) :
    SD.twoAt f01 f02 f03 c ∨ SD.twoAt f01 f12 f13 c ∨ SD.twoAt f02 f12 f23 c ∨
      SD.twoAt f03 f13 f23 c := by
  by_contra hm
  cases c <;> cases f01 <;> cases f02 <;> cases f03 <;> cases f12 <;> cases f13 <;> cases f23 <;>
    simp only [SD.twoAt, Bool.true_eq_false, Bool.false_eq_true, and_true, and_false, or_false,
      or_true, not_true_eq_false, not_false_eq_true, if_true, if_false] at hm hsum <;>
    linarith

/-- `key_bool` with weights `|t_ij|` and flags `decide (t_ij < 0)`. -/
theorem key_t (t01 t02 t03 t12 t13 t23 w01 w02 w03 w12 w13 w23 : ℝ)
    (f01 f02 f03 f12 f13 f23 : Bool)
    (e01 : f01 = decide (t01 < 0)) (e02 : f02 = decide (t02 < 0)) (e03 : f03 = decide (t03 < 0))
    (e12 : f12 = decide (t12 < 0)) (e13 : f13 = decide (t13 < 0)) (e23 : f23 = decide (t23 < 0))
    (a01 : |t01| = w01) (a02 : |t02| = w02) (a03 : |t03| = w03)
    (a12 : |t12| = w12) (a13 : |t13| = w13) (a23 : |t23| = w23)
    (hsum : t01 + t02 + t03 + t12 + t13 + t23 = 0)
    (h0a : w01 < w02 + w03) (h0b : w02 < w01 + w03) (h0c : w03 < w01 + w02)
    (h1a : w01 < w12 + w13) (h1b : w12 < w01 + w13) (h1c : w13 < w01 + w12)
    (h2a : w02 < w12 + w23) (h2b : w12 < w02 + w23) (h2c : w23 < w02 + w12)
    (h3a : w03 < w13 + w23) (h3b : w13 < w03 + w23) (h3c : w23 < w03 + w13) (c : Bool) :
    SD.twoAt f01 f02 f03 c ∨ SD.twoAt f01 f12 f13 c ∨ SD.twoAt f02 f12 f23 c ∨
      SD.twoAt f03 f13 f23 c := by
  subst e01 e02 e03 e12 e13 e23 a01 a02 a03 a12 a13 a23
  refine key_bool _ _ _ _ _ _ _ _ _ _ _ _ h0a h0b h0c h1a h1b h1c h2a h2b h2c h3a h3b h3c ?_ c
  rw [ite_abs, ite_abs, ite_abs, ite_abs, ite_abs, ite_abs]
  exact hsum

/-! ### Vector identities -/

theorem sum_alpha (u0 u1 u2 u3 : V3) :
    det u1 u2 u3 • u0 + (-det u0 u2 u3) • u1 + det u0 u1 u3 • u2 + (-det u0 u1 u2) • u3 = 0 := by
  ext <;> simp only [add_x, add_y, add_z, smul_x, smul_y, smul_z, zero_x, zero_y, zero_z,
    det_eq] <;> ring

theorem T_eq (p q u v : V3) : det (p - q) u v = dot u (cross q v) + dot (cross p u) v := by
  simp only [det_eq, dot, cross_x, cross_y, cross_z, sub_x, sub_y, sub_z]; ring

theorem bilin (a0 a1 a2 a3 : ℝ) (u0 u1 u2 u3 m0 m1 m2 m3 : V3) :
    a0 * a1 * (dot u0 m1 + dot m0 u1) + a0 * a2 * (dot u0 m2 + dot m0 u2)
      + a0 * a3 * (dot u0 m3 + dot m0 u3) + a1 * a2 * (dot u1 m2 + dot m1 u2)
      + a1 * a3 * (dot u1 m3 + dot m1 u3) + a2 * a3 * (dot u2 m3 + dot m2 u3)
    = dot (a0 • u0 + a1 • u1 + a2 • u2 + a3 • u3) (a0 • m0 + a1 • m1 + a2 • m2 + a3 • m3)
      - (a0 ^ 2 * dot u0 m0 + a1 ^ 2 * dot u1 m1 + a2 ^ 2 * dot u2 m2 + a3 ^ 2 * dot u3 m3) := by
  simp only [dot, add_x, add_y, add_z, smul_x, smul_y, smul_z]; ring

/-- Step (ii): `Σ_{i<j} α_i α_j T_{ij} = 0` whenever `Σ α_k u_k = 0`. -/
theorem circ_sum (a0 a1 a2 a3 : ℝ) (u0 u1 u2 u3 p0 p1 p2 p3 : V3)
    (h : a0 • u0 + a1 • u1 + a2 • u2 + a3 • u3 = 0) :
    a0 * a1 * det (p0 - p1) u0 u1 + a0 * a2 * det (p0 - p2) u0 u2 + a0 * a3 * det (p0 - p3) u0 u3
      + a1 * a2 * det (p1 - p2) u1 u2 + a1 * a3 * det (p1 - p3) u1 u3
      + a2 * a3 * det (p2 - p3) u2 u3 = 0 := by
  simp only [T_eq]
  rw [bilin a0 a1 a2 a3 u0 u1 u2 u3 (cross p0 u0) (cross p1 u1) (cross p2 u2) (cross p3 u3), h,
    dot_cross_self_right, dot_cross_self_right, dot_cross_self_right, dot_cross_self_right]
  simp only [dot, zero_x, zero_y, zero_z]; ring

theorem norm2_add (b c : V3) : norm2 (b + c) = norm2 b + norm2 c + 2 * dot b c := by
  simp only [norm2, dot, add_x, add_y, add_z]; ring

theorem norm2_smul (k : ℝ) (a : V3) : norm2 (k • a) = k ^ 2 * norm2 a := by
  simp only [norm2, dot, smul_x, smul_y, smul_z]; ring

theorem norm2_cross_smul (a b : ℝ) (u v : V3) :
    norm2 (cross (a • u) (b • v)) = (a * b) ^ 2 * norm2 (cross u v) := by
  simp only [norm2, dot, cross_x, cross_y, cross_z, smul_x, smul_y, smul_z]; ring

theorem norm2_cross_comm (a b : V3) : norm2 (cross a b) = norm2 (cross b a) := by
  simp only [norm2, dot, cross_x, cross_y, cross_z]; ring

theorem det_smul (a b c : ℝ) (u v w : V3) : det (a • u) (b • v) (c • w) = a * b * c * det u v w := by
  simp only [det_eq, smul_x, smul_y, smul_z]; ring

theorem cross_cross_same (a c d : V3) : cross (cross a c) (cross a d) = det a c d • a := by
  ext <;> simp only [cross_x, cross_y, cross_z, smul_x, smul_y, smul_z, det_eq] <;> ring

theorem sum4_perm {a b c d : V3} (h : a + b + c + d = 0) :
    b + a + c + d = 0 ∧ c + a + b + d = 0 ∧ d + a + b + c = 0 := by
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp only [add_x, add_y, add_z, zero_x, zero_y, zero_z] at hx hy hz
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp only [add_x, add_y, add_z, zero_x, zero_y, zero_z] <;>
    linarith

/-! ### Strict triangle inequalities -/

/-- Strict triangle inequality for non-parallel vectors (Lagrange identity). -/
theorem strict_tri (b c : V3) (h : 0 < norm2 (cross b c)) :
    √(norm2 (b + c)) < √(norm2 b) + √(norm2 c) := by
  have hL := norm2_cross b c
  have hnb := norm2_nonneg b
  have hnc := norm2_nonneg c
  have hsb := Real.sq_sqrt hnb
  have hsc := Real.sq_sqrt hnc
  have h0b := Real.sqrt_nonneg (norm2 b)
  have h0c := Real.sqrt_nonneg (norm2 c)
  have hd : dot b c < √(norm2 b) * √(norm2 c) := by
    have h1 : dot b c ^ 2 < (√(norm2 b) * √(norm2 c)) ^ 2 := by
      rw [mul_pow, hsb, hsc]; linarith
    exact lt_of_abs_lt (abs_lt_of_sq_lt_sq h1 (mul_nonneg h0b h0c))
  rw [← Real.sqrt_sq (add_nonneg h0b h0c)]
  apply Real.sqrt_lt_sqrt (norm2_nonneg _)
  rw [norm2_add, add_sq, hsb, hsc]
  linarith

theorem tri_vec (P Q R : V3) (h : P + Q + R = 0) (hQR : 0 < norm2 (cross Q R)) :
    √(norm2 P) < √(norm2 Q) + √(norm2 R) := by
  have hP : norm2 P = norm2 (Q + R) := by
    have hx := congrArg V3.x h
    have hy := congrArg V3.y h
    have hz := congrArg V3.z h
    simp only [add_x, add_y, add_z, zero_x, zero_y, zero_z] at hx hy hz
    have ex : P.x = -(Q.x + R.x) := by linarith
    have ey : P.y = -(Q.y + R.y) := by linarith
    have ez : P.z = -(Q.z + R.z) := by linarith
    simp only [norm2, dot, add_x, add_y, add_z, ex, ey, ez]; ring
  rw [hP]
  exact strict_tri Q R hQR

/-- Step (iv): for `a + b + c + d = 0` with `det a b c ≠ 0`, the three vectors `a × b`, `a × c`,
`a × d` (which sum to zero and are pairwise non-parallel) satisfy strict triangle inequalities. -/
theorem vtx (a b c d : V3) (h : a + b + c + d = 0) (hdet : det a b c ≠ 0) :
    √(norm2 (cross a b)) < √(norm2 (cross a c)) + √(norm2 (cross a d)) ∧
    √(norm2 (cross a c)) < √(norm2 (cross a b)) + √(norm2 (cross a d)) ∧
    √(norm2 (cross a d)) < √(norm2 (cross a b)) + √(norm2 (cross a c)) := by
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp only [add_x, add_y, add_z, zero_x, zero_y, zero_z] at hx hy hz
  have hd : d = -(a + b + c) := by
    ext <;> simp only [neg_x, neg_y, neg_z, add_x, add_y, add_z] <;> linarith
  subst hd
  have ha : 0 < norm2 a := by
    rcases (norm2_nonneg a).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      apply hdet
      rw [(norm2_eq_zero_iff a).mp h'.symm]
      simp only [det_eq, zero_x, zero_y, zero_z]; ring
  have pos : ∀ e f : V3, det a e f ≠ 0 → 0 < norm2 (cross (cross a e) (cross a f)) := by
    intro e f hef
    rw [cross_cross_same, norm2_smul]
    positivity
  have d1 : det a c (-(a + b + c)) ≠ 0 := by
    rw [show det a c (-(a + b + c)) = det a b c by
      simp only [det_eq, neg_x, neg_y, neg_z, add_x, add_y, add_z]; ring]
    exact hdet
  have d2 : det a b (-(a + b + c)) ≠ 0 := by
    rw [show det a b (-(a + b + c)) = -det a b c by
      simp only [det_eq, neg_x, neg_y, neg_z, add_x, add_y, add_z]; ring]
    exact neg_ne_zero.mpr hdet
  refine ⟨tri_vec _ _ _ ?_ (pos _ _ d1), tri_vec _ _ _ ?_ (pos _ _ d2),
    tri_vec _ _ _ ?_ (pos _ _ hdet)⟩ <;>
    ext <;> simp only [cross_x, cross_y, cross_z, neg_x, neg_y, neg_z, add_x, add_y, add_z,
      zero_x, zero_y, zero_z] <;> ring

/-! ### Assembly -/

theorem circ_core (α0 α1 α2 α3 : ℝ) (u0 u1 u2 u3 p0 p1 p2 p3 : V3)
    (T01 T02 T03 T12 T13 T23 : ℝ)
    (hα : α0 • u0 + α1 • u1 + α2 • u2 + α3 • u3 = 0)
    (hα0 : α0 ≠ 0) (hα1 : α1 ≠ 0) (hα2 : α2 ≠ 0) (hα3 : α3 ≠ 0)
    (d012 : det u0 u1 u2 ≠ 0) (d013 : det u0 u1 u3 ≠ 0)
    (e01 : T01 = det (p0 - p1) u0 u1) (e02 : T02 = det (p0 - p2) u0 u2)
    (e03 : T03 = det (p0 - p3) u0 u3) (e12 : T12 = det (p1 - p2) u1 u2)
    (e13 : T13 = det (p1 - p3) u1 u3) (e23 : T23 = det (p2 - p3) u2 u3)
    (q01 : T01 ^ 2 = norm2 (cross u0 u1)) (q02 : T02 ^ 2 = norm2 (cross u0 u2))
    (q03 : T03 ^ 2 = norm2 (cross u0 u3)) (q12 : T12 ^ 2 = norm2 (cross u1 u2))
    (q13 : T13 ^ 2 = norm2 (cross u1 u3)) (q23 : T23 ^ 2 = norm2 (cross u2 u3)) (c : Bool) :
    SD.twoAt (decide (α0 * α1 * T01 < 0)) (decide (α0 * α2 * T02 < 0))
        (decide (α0 * α3 * T03 < 0)) c ∨
      SD.twoAt (decide (α0 * α1 * T01 < 0)) (decide (α1 * α2 * T12 < 0))
        (decide (α1 * α3 * T13 < 0)) c ∨
      SD.twoAt (decide (α0 * α2 * T02 < 0)) (decide (α1 * α2 * T12 < 0))
        (decide (α2 * α3 * T23 < 0)) c ∨
      SD.twoAt (decide (α0 * α3 * T03 < 0)) (decide (α1 * α3 * T13 < 0))
        (decide (α2 * α3 * T23 < 0)) c := by
  have hsum : α0 * α1 * T01 + α0 * α2 * T02 + α0 * α3 * T03 + α1 * α2 * T12 + α1 * α3 * T13
      + α2 * α3 * T23 = 0 := by
    rw [e01, e02, e03, e12, e13, e23]
    exact circ_sum _ _ _ _ _ _ _ _ p0 p1 p2 p3 hα
  have ab : ∀ {a b T : ℝ} {u v : V3}, T ^ 2 = norm2 (cross u v) →
      |a * b * T| = √(norm2 (cross (a • u) (b • v))) := by
    intro a b T u v hq
    rw [← Real.sqrt_sq_eq_abs, norm2_cross_smul, ← hq]
    congr 1
    ring
  have a01 : |α0 * α1 * T01| = √(norm2 (cross (α0 • u0) (α1 • u1))) := ab q01
  have a02 : |α0 * α2 * T02| = √(norm2 (cross (α0 • u0) (α2 • u2))) := ab q02
  have a03 : |α0 * α3 * T03| = √(norm2 (cross (α0 • u0) (α3 • u3))) := ab q03
  have a12 : |α1 * α2 * T12| = √(norm2 (cross (α1 • u1) (α2 • u2))) := ab q12
  have a13 : |α1 * α3 * T13| = √(norm2 (cross (α1 • u1) (α3 • u3))) := ab q13
  have a23 : |α2 * α3 * T23| = √(norm2 (cross (α2 • u2) (α3 • u3))) := ab q23
  obtain ⟨S1, S2, S3⟩ := sum4_perm hα
  have D0 : det (α0 • u0) (α1 • u1) (α2 • u2) ≠ 0 := by
    rw [det_smul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hα0 hα1) hα2) d012
  have D1 : det (α1 • u1) (α0 • u0) (α2 • u2) ≠ 0 := by
    rw [det_smul, det_swap12]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hα1 hα0) hα2) (neg_ne_zero.mpr d012)
  have D2 : det (α2 • u2) (α0 • u0) (α1 • u1) ≠ 0 := by
    rw [det_smul, show det u2 u0 u1 = det u0 u1 u2 by simp only [det_eq]; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hα2 hα0) hα1) d012
  have D3 : det (α3 • u3) (α0 • u0) (α1 • u1) ≠ 0 := by
    rw [det_smul, show det u3 u0 u1 = det u0 u1 u3 by simp only [det_eq]; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hα3 hα0) hα1) d013
  obtain ⟨t0a, t0b, t0c⟩ := vtx _ _ _ _ hα D0
  obtain ⟨t1a, t1b, t1c⟩ := vtx _ _ _ _ S1 D1
  obtain ⟨t2a, t2b, t2c⟩ := vtx _ _ _ _ S2 D2
  obtain ⟨t3a, t3b, t3c⟩ := vtx _ _ _ _ S3 D3
  rw [norm2_cross_comm (α1 • u1) (α0 • u0)] at t1a t1b t1c
  rw [norm2_cross_comm (α2 • u2) (α0 • u0), norm2_cross_comm (α2 • u2) (α1 • u1)] at t2a t2b t2c
  rw [norm2_cross_comm (α3 • u3) (α0 • u0), norm2_cross_comm (α3 • u3) (α1 • u1),
    norm2_cross_comm (α3 • u3) (α2 • u2)] at t3a t3b t3c
  exact key_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl a01 a02 a03 a12 a13 a23
    hsum t0a t0b t0c t1a t1b t1c t2a t2b t2c t3a t3b t3c c

end Circuit

theorem UFam.sd_circ (F : UFam) : F.sd.Circ := by
  intro v0 v1 v2 v3 hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hnd
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := hnd
  have d123 := F.det_ne h12 h13 h23
  have d023 := F.det_ne h02 h03 h23
  have d013 := F.det_ne h01 h03 h13
  have d012 := F.det_ne h01 h02 h12
  have n1 : -det (F.u v0) (F.u v2) (F.u v3) ≠ 0 := neg_ne_zero.mpr d023
  have n3 : -det (F.u v0) (F.u v1) (F.u v2) ≠ 0 := neg_ne_zero.mpr d012
  simp only [SD.CircInst, UFam.sd_neg3, UFam.sd_neg2]
  intro c
  rw [← Circuit.flag_neg d023, ← Circuit.flag_neg d012, Circuit.flag3 (F.T_ne h01) d123 n1,
    Circuit.flag3 (F.T_ne h02) d123 d013, Circuit.flag3 (F.T_ne h03) d123 n3,
    Circuit.flag3 (F.T_ne h12) n1 d013, Circuit.flag3 (F.T_ne h13) n1 n3,
    Circuit.flag3 (F.T_ne h23) d013 n3]
  exact Circuit.circ_core (det (F.u v1) (F.u v2) (F.u v3)) (-det (F.u v0) (F.u v2) (F.u v3))
    (det (F.u v0) (F.u v1) (F.u v3)) (-det (F.u v0) (F.u v1) (F.u v2))
    (F.u v0) (F.u v1) (F.u v2) (F.u v3) (F.p v0) (F.p v1) (F.p v2) (F.p v3)
    (F.T v0 v1) (F.T v0 v2) (F.T v0 v3) (F.T v1 v2) (F.T v1 v3) (F.T v2 v3)
    (Circuit.sum_alpha _ _ _ _) d123 n1 d013 n3 d012 d013 rfl rfl rfl rfl rfl rfl
    (F.T_sq h01) (F.T_sq h02) (F.T_sq h03) (F.T_sq h12) (F.T_sq h13) (F.T_sq h23) c

end Results.EightEquidistantLines
