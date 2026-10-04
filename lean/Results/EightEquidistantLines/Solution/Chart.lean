import Results.EightEquidistantLines.Solution.NoParallel
import Results.EightEquidistantLines.Solution.Signs
import Results.EightEquidistantLines.Solution.Obstruction

/-!
# The two-base chart (paper, Section 4)

For base labels `r, s` and three further labels `lab 0, lab 1, lab 2` of a unit-distance family,
reorient the directions by `g_r = 1`, `g_v = ε_{rv}` so that every `T_{rv}` is positive, take the
frame `e_z = u_r`, `e_x ∝ -(u_r × u_s)`, `e_y = e_z × e_x`, with origin the closest point of the line
`r` to the line `s`, and write each further line as
`(0,h,(kh + A + H)/e) + t (1,a,(ka - A)/e)` with `h² - a² = 1`, `H² - A² = 1`.

`UFam.chart` packages the output: reals `h a H A` on the three labels with the hyperbola equations,
distinct `a`'s and `A`'s, and the sign dictionary (paper (4.2)/(sign-only form)): the signs of
`h_v, H_v, a_w - a_v, A_w - A_v` and `w_{vw}` are those of the flags `hF, HF, aF, AF, wF` of
`Spec.lean` (formulas of the paper's displayed "sign-only form", for the original orientation).

## Method: the chart in invariant form

The frame, the closest points, the reorientation and the rescaling `ū_v = u'_v / x_v` of the paper
all cancel out of the chart coordinates.  Writing `D_v = det(u_r, u_s, u_v)` (non-zero by triple
independence), the paper's rescaled direction is `ū_v = -(T_{rs}/D_v) u_v`, and the coordinates are
* `h_v = T_{rs} T_{rv} / D_v` (the paper's `h_v = -T̄_{rv}`),
* `a_v = -((u_r × u_s)·(u_r × u_v)) / D_v`,
* `(H_v, A_v) = ε_{rs} (h'_v, a'_v)` where `h', a'` are the same expressions for the swapped
  bases `(s, r)` (the paper's `H_v = e T̄_{sv}` and `A_v = k a_v - e b_v`).
(These agree with the coordinates of `notes/chart_reference.py` up to rounding; the proof below does
not depend on that comparison, it verifies the stated properties directly.)

The hyperbola equations are the Lagrange identity
`‖u_r×u_s‖²‖u_r×u_v‖² - ((u_r×u_s)·(u_r×u_v))² = D_v² ‖u_r‖²` combined with `T_{ij}² = ‖u_i×u_j‖²`;
`a_w - a_v = ‖u_r×u_s‖² det(u_r,u_v,u_w) / (D_v D_w)` is a polynomial identity; and
`w_{vw} = -T_{vw} D_v D_w / (T_{rs} det(u_r,u_v,u_w) det(u_s,u_v,u_w))` is the four-line identity
`Σ_{i<j} α_i α_j T_{v_i v_j} = 0` of Lemma 3.1 for the labels `(r, s, v, w)`.  The signs are then
read off factor by factor.
-/

namespace Results.EightEquidistantLines

open V3

namespace Chart

/-! ### Sign bookkeeping: negativity flags of products and quotients -/

/-- Negativity flag of a product of non-zero reals. -/
theorem negb_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (x * y < 0) = (decide (x < 0) ^^ decide (y < 0)) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · rw [decide_eq_false (not_lt.mpr (mul_pos_of_neg_of_neg hx hy).le), decide_eq_true hx,
      decide_eq_true hy]; rfl
  · rw [decide_eq_true (mul_neg_of_neg_of_pos hx hy), decide_eq_true hx,
      decide_eq_false (not_lt.mpr hy.le)]; rfl
  · rw [decide_eq_true (mul_neg_of_pos_of_neg hx hy), decide_eq_false (not_lt.mpr hx.le),
      decide_eq_true hy]; rfl
  · rw [decide_eq_false (not_lt.mpr (mul_pos hx hy).le), decide_eq_false (not_lt.mpr hx.le),
      decide_eq_false (not_lt.mpr hy.le)]; rfl

theorem negb_inv (x : ℝ) : decide (x⁻¹ < 0) = decide (x < 0) :=
  decide_eq_decide.mpr inv_neg''

/-- Negativity flag of a quotient of non-zero reals. -/
theorem negb_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (x / y < 0) = (decide (x < 0) ^^ decide (y < 0)) := by
  rw [div_eq_mul_inv, negb_mul hx (inv_ne_zero hy), negb_inv]

theorem negb_neg {x : ℝ} (hx : x ≠ 0) : decide (-x < 0) = !decide (x < 0) := by
  rcases hx.lt_or_gt with hx | hx
  · rw [decide_eq_false (not_lt.mpr (neg_pos.mpr hx).le), decide_eq_true hx]; rfl
  · rw [decide_eq_true (neg_lt_zero.mpr hx), decide_eq_false (not_lt.mpr hx.le)]; rfl

theorem negb_of_pos {x : ℝ} (hx : 0 < x) : decide (x < 0) = false :=
  decide_eq_false (not_lt.mpr hx.le)

theorem iff_of_decide {p : Prop} [Decidable p] {b : Bool} (h : decide p = b) :
    p ↔ b = true := by
  rw [← h, decide_eq_true_iff]

theorem bool_H (b1 b2 b3 : Bool) : (b1 ^^ ((b1 ^^ b2) ^^ !b3)) = (true ^^ b2 ^^ b3) := by
  revert b1 b2 b3; decide

theorem bool_a (b1 b2 b3 : Bool) : ((false ^^ b1) ^^ (b2 ^^ b3)) = (b2 ^^ b3 ^^ b1) := by
  revert b1 b2 b3; decide

theorem bool_A (b0 b1 b2 b3 : Bool) :
    (b0 ^^ ((false ^^ b1) ^^ ((!b2) ^^ !b3))) = (b0 ^^ b2 ^^ b3 ^^ b1) := by
  revert b0 b1 b2 b3; decide

theorem bool_w (a b c d e f : Bool) :
    (!(((a ^^ b) ^^ c) ^^ ((d ^^ e) ^^ f))) = (true ^^ d ^^ a ^^ b ^^ c ^^ e ^^ f) := by
  revert a b c d e f; decide

/-! ### Vector identities -/

/-- Lagrange identity for `u_r × u_s` and `u_r × u_v` (their cross product is `det · u_r`). -/
theorem hyp_id (a b c : V3) :
    norm2 (cross a b) * norm2 (cross a c) - dot (cross a b) (cross a c) ^ 2
      = det a b c ^ 2 * norm2 a := by
  simp only [norm2, dot, cross_x, cross_y, cross_z, det_eq]; ring

/-- The numerator of `a_w - a_v`. -/
theorem diff_id (a b v w : V3) :
    dot (cross a b) (cross a v) * det a b w - dot (cross a b) (cross a w) * det a b v
      = norm2 (cross a b) * det a v w := by
  simp only [norm2, dot, cross_x, cross_y, cross_z, det_eq]; ring

/-- `Σ_k α_k u_k = 0` for four vectors, dotted with an arbitrary `m`
(`α_k = (-1)^k det(.., omit k, ..)`). -/
theorem sum_alpha_dot (u0 u1 u2 u3 m : V3) :
    det u1 u2 u3 * dot u0 m - det u0 u2 u3 * dot u1 m + det u0 u1 u3 * dot u2 m
      - det u0 u1 u2 * dot u3 m = 0 := by
  simp only [dot, det_eq]; ring

/-- `T_{ij} = u_j · m_i + u_i · m_j` with moments `m = p × u`. -/
theorem T_split (pi pj ui uj : V3) :
    det (pi - pj) ui uj = dot uj (cross pi ui) + dot ui (cross pj uj) := by
  simp only [det_eq, dot, cross_x, cross_y, cross_z, sub_x, sub_y, sub_z]; ring

/-- The four-line identity `Σ_{i<j} α_i α_j T_{v_i v_j} = 0` (paper, proof of Lemma 3.1) for the
labels `(r, s, v, w)`, written with `T_{ij} = det(p_i - p_j, u_i, u_j)`. -/
theorem circuit_id (pr ps pv pw ur us uv uw : V3) :
    det (pr - ps) ur us * det ur uv uw * det us uv uw
    + (det (pr - pw) ur uw * det ur us uv - det (pr - pv) ur uv * det ur us uw) * det us uv uw
    - (det (ps - pw) us uw * det ur us uv - det (ps - pv) us uv * det ur us uw) * det ur uv uw
    + det (pv - pw) uv uw * det ur us uv * det ur us uw = 0 := by
  rw [T_split pr ps, T_split pr pw, T_split pr pv, T_split ps pw, T_split ps pv, T_split pv pw]
  have e0 := sum_alpha_dot ur us uv uw (cross pr ur)
  have e1 := sum_alpha_dot ur us uv uw (cross ps us)
  have e2 := sum_alpha_dot ur us uv uw (cross pv uv)
  have e3 := sum_alpha_dot ur us uv uw (cross pw uw)
  have d0 := dot_cross_self_right pr ur
  have d1 := dot_cross_self_right ps us
  have d2 := dot_cross_self_right pv uv
  have d3 := dot_cross_self_right pw uw
  linear_combination (-det us uv uw) * e0 + (det ur uv uw) * e1 - (det ur us uw) * e2
    + (det ur us uv) * e3 + (det us uv uw) ^ 2 * d0 + (det ur uv uw) ^ 2 * d1
    + (det ur us uw) ^ 2 * d2 + (det ur us uv) ^ 2 * d3

/-! ### Chart quantities in invariant form -/

/-- The chart coordinate `h_v = T_{rs} T_{rv} / det(u_r, u_s, u_v)` for the bases `r, s`. -/
noncomputable def ch (F : UFam) (r s v : Fin 8) : ℝ :=
  F.T r s * F.T r v / det (F.u r) (F.u s) (F.u v)

/-- The chart coordinate `a_v = -((u_r × u_s)·(u_r × u_v)) / det(u_r, u_s, u_v)`. -/
noncomputable def ca (F : UFam) (r s v : Fin 8) : ℝ :=
  -dot (cross (F.u r) (F.u s)) (cross (F.u r) (F.u v)) / det (F.u r) (F.u s) (F.u v)

/-- The sign `ε_{rs}` as a real number. -/
noncomputable def sg (F : UFam) (r s : Fin 8) : ℝ := if F.T r s < 0 then -1 else 1

variable (F : UFam)

theorem ch_hyp {r s v : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hsv : s ≠ v) :
    ch F r s v ^ 2 - ca F r s v ^ 2 = 1 := by
  have hD := F.det_ne hrs hrv hsv
  have key := hyp_id (F.u r) (F.u s) (F.u v)
  rw [F.unit r, mul_one, ← F.T_sq hrs, ← F.T_sq hrv] at key
  unfold ch ca
  field_simp
  linear_combination key

theorem ca_sub {r s v w : Fin 8} (hv : det (F.u r) (F.u s) (F.u v) ≠ 0)
    (hw : det (F.u r) (F.u s) (F.u w) ≠ 0) :
    ca F r s w - ca F r s v = norm2 (cross (F.u r) (F.u s)) * det (F.u r) (F.u v) (F.u w) /
      (det (F.u r) (F.u s) (F.u v) * det (F.u r) (F.u s) (F.u w)) := by
  have key := diff_id (F.u r) (F.u s) (F.u v) (F.u w)
  unfold ca
  field_simp
  linear_combination key

theorem M_pos {r s : Fin 8} (hrs : r ≠ s) : 0 < norm2 (cross (F.u r) (F.u s)) := by
  rw [← F.T_sq hrs]; exact sq_pos_of_ne_zero (F.T_ne hrs)

/-- The divided difference `(h_w - h_v)/(a_w - a_v)` in invariant form. -/
theorem ch_ratio {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) :
    (ch F r s w - ch F r s v) / (ca F r s w - ca F r s v) =
      (F.T r w * det (F.u r) (F.u s) (F.u v) - F.T r v * det (F.u r) (F.u s) (F.u w)) /
        (F.T r s * det (F.u r) (F.u v) (F.u w)) := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hE := F.det_ne hrv hrw hvw
  have hT := F.T_ne hrs
  rw [ca_sub F hv hw, ← F.T_sq hrs]
  unfold ch
  field_simp

theorem sg_sq (r s : Fin 8) : sg F r s ^ 2 = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem sg_ne (r s : Fin 8) : sg F r s ≠ 0 := by
  unfold sg; split_ifs <;> norm_num

theorem negb_sg (r s : Fin 8) : decide (sg F r s < 0) = decide (F.T r s < 0) := by
  unfold sg
  split_ifs with h
  · rw [decide_eq_true (by norm_num : (-1 : ℝ) < 0), decide_eq_true h]
  · rw [decide_eq_false (by norm_num : ¬ (1 : ℝ) < 0), decide_eq_false h]

theorem H_hyp {r s v : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hsv : s ≠ v) :
    (sg F r s * ch F s r v) ^ 2 - (sg F r s * ca F s r v) ^ 2 = 1 := by
  rw [mul_pow, mul_pow, ← mul_sub, sg_sq, one_mul]
  exact ch_hyp F hrs.symm hsv hrv

/-! ### The sign dictionary -/

theorem h_sign {r s v : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hsv : s ≠ v) :
    decide (ch F r s v < 0) = F.sd.hF r s v := by
  have hD := F.det_ne hrs hrv hsv
  unfold ch
  rw [negb_div (mul_ne_zero (F.T_ne hrs) (F.T_ne hrv)) hD, negb_mul (F.T_ne hrs) (F.T_ne hrv)]
  rfl

theorem H_sign {r s v : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hsv : s ≠ v) :
    decide (sg F r s * ch F s r v < 0) = F.sd.HF r s v := by
  have hD := F.det_ne hrs hrv hsv
  have hD' := F.det_ne hrs.symm hsv hrv
  have hT := mul_ne_zero (F.T_ne hrs.symm) (F.T_ne hsv)
  unfold ch
  rw [negb_mul (sg_ne F r s) (div_ne_zero hT hD'), negb_sg,
    negb_div hT hD', negb_mul (F.T_ne hrs.symm) (F.T_ne hsv), F.T_symm r s,
    det_swap12 (F.u r) (F.u s) (F.u v), negb_neg hD]
  exact bool_H _ _ _

theorem a_sign {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) :
    decide (ca F r s w - ca F r s v < 0) = F.sd.aF r s v w := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hE := F.det_ne hrv hrw hvw
  have hM := M_pos F hrs
  rw [ca_sub F hv hw, negb_div (mul_ne_zero hM.ne' hE) (mul_ne_zero hv hw), negb_mul hM.ne' hE,
    negb_mul hv hw, negb_of_pos hM]
  exact bool_a _ _ _

theorem ca_ne {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) : ca F r s v ≠ ca F r s w := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hE := F.det_ne hrv hrw hvw
  have hM := M_pos F hrs
  intro h
  have h0 : ca F r s w - ca F r s v = 0 := by rw [h, sub_self]
  rw [ca_sub F hv hw] at h0
  exact div_ne_zero (mul_ne_zero hM.ne' hE) (mul_ne_zero hv hw) h0

theorem A_sign {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) :
    decide (sg F r s * ca F s r w - sg F r s * ca F s r v < 0) = F.sd.AF r s v w := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hv' := F.det_ne hrs.symm hsv hrv
  have hw' := F.det_ne hrs.symm hsw hrw
  have hE := F.det_ne hsv hsw hvw
  have hM := M_pos F hrs.symm
  rw [← mul_sub, ca_sub F hv' hw',
    negb_mul (sg_ne F r s) (div_ne_zero (mul_ne_zero hM.ne' hE) (mul_ne_zero hv' hw')), negb_sg,
    negb_div (mul_ne_zero hM.ne' hE) (mul_ne_zero hv' hw'), negb_mul hM.ne' hE,
    negb_mul hv' hw', negb_of_pos hM, det_swap12 (F.u r) (F.u s) (F.u v),
    det_swap12 (F.u r) (F.u s) (F.u w), negb_neg hv, negb_neg hw]
  exact bool_A _ _ _ _

theorem A_ne {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) : sg F r s * ca F s r v ≠ sg F r s * ca F s r w := by
  intro h
  exact ca_ne F hrs.symm hsv hsw hrv hrw hvw (mul_left_cancel₀ (sg_ne F r s) h)

/-! ### The quantity `w_{vw}` -/

/-- `w_{vw} = -T_{vw} D_v D_w / (T_{rs} det(u_r,u_v,u_w) det(u_s,u_v,u_w))`. -/
theorem w_eq {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) :
    1 + (ch F r s w - ch F r s v) / (ca F r s w - ca F r s v)
      + (sg F r s * ch F s r w - sg F r s * ch F s r v) /
        (sg F r s * ca F s r w - sg F r s * ca F s r v)
    = -(F.T v w * det (F.u r) (F.u s) (F.u v) * det (F.u r) (F.u s) (F.u w) /
        (F.T r s * det (F.u r) (F.u v) (F.u w) * det (F.u s) (F.u v) (F.u w))) := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hEr := F.det_ne hrv hrw hvw
  have hEs := F.det_ne hsv hsw hvw
  have hT := F.T_ne hrs
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ (sg_ne F r s), ch_ratio F hrs hrv hrw hsv hsw hvw,
    ch_ratio F hrs.symm hsv hsw hrv hrw hvw, F.T_symm r s, det_swap12 (F.u r) (F.u s) (F.u v),
    det_swap12 (F.u r) (F.u s) (F.u w)]
  have circ : F.T r s * det (F.u r) (F.u v) (F.u w) * det (F.u s) (F.u v) (F.u w)
      + (F.T r w * det (F.u r) (F.u s) (F.u v) - F.T r v * det (F.u r) (F.u s) (F.u w))
        * det (F.u s) (F.u v) (F.u w)
      - (F.T s w * det (F.u r) (F.u s) (F.u v) - F.T s v * det (F.u r) (F.u s) (F.u w))
        * det (F.u r) (F.u v) (F.u w)
      + F.T v w * det (F.u r) (F.u s) (F.u v) * det (F.u r) (F.u s) (F.u w) = 0 :=
    circuit_id (F.p r) (F.p s) (F.p v) (F.p w) (F.u r) (F.u s) (F.u v) (F.u w)
  field_simp
  linear_combination circ

theorem w_sign {r s v w : Fin 8} (hrs : r ≠ s) (hrv : r ≠ v) (hrw : r ≠ w) (hsv : s ≠ v)
    (hsw : s ≠ w) (hvw : v ≠ w) :
    -(F.T v w * det (F.u r) (F.u s) (F.u v) * det (F.u r) (F.u s) (F.u w) /
        (F.T r s * det (F.u r) (F.u v) (F.u w) * det (F.u s) (F.u v) (F.u w))) ≠ 0 ∧
    decide (-(F.T v w * det (F.u r) (F.u s) (F.u v) * det (F.u r) (F.u s) (F.u w) /
        (F.T r s * det (F.u r) (F.u v) (F.u w) * det (F.u s) (F.u v) (F.u w))) < 0)
      = F.sd.wF r s v w := by
  have hv := F.det_ne hrs hrv hsv
  have hw := F.det_ne hrs hrw hsw
  have hEr := F.det_ne hrv hrw hvw
  have hEs := F.det_ne hsv hsw hvw
  have hT := F.T_ne hrs
  have hTvw := F.T_ne hvw
  have hnum := mul_ne_zero (mul_ne_zero hTvw hv) hw
  have hden := mul_ne_zero (mul_ne_zero hT hEr) hEs
  refine ⟨neg_ne_zero.mpr (div_ne_zero hnum hden), ?_⟩
  rw [negb_neg (div_ne_zero hnum hden), negb_div hnum hden, negb_mul (mul_ne_zero hTvw hv) hw,
    negb_mul hTvw hv, negb_mul (mul_ne_zero hT hEr) hEs, negb_mul hT hEr]
  exact bool_w _ _ _ _ _ _

end Chart

theorem UFam.chart (F : UFam) (r s : Fin 8) (lab : Fin 3 → Fin 8)
    (hnd : [r, s, lab 0, lab 1, lab 2].Nodup) :
    ∃ h a H A : Fin 3 → ℝ,
      (∀ v, h v ^ 2 - a v ^ 2 = 1) ∧ (∀ v, H v ^ 2 - A v ^ 2 = 1) ∧
      (∀ v w, v ≠ w → a v ≠ a w) ∧ (∀ v w, v ≠ w → A v ≠ A w) ∧
      (∀ v, (h v < 0 ↔ F.sd.hF r s (lab v) = true)) ∧
      (∀ v, (H v < 0 ↔ F.sd.HF r s (lab v) = true)) ∧
      (∀ v w, v ≠ w → (a w - a v < 0 ↔ F.sd.aF r s (lab v) (lab w) = true)) ∧
      (∀ v w, v ≠ w → (A w - A v < 0 ↔ F.sd.AF r s (lab v) (lab w) = true)) ∧
      (∀ v w, v ≠ w → (wval h a H A v w ≠ 0 ∧
        (wval h a H A v w < 0 ↔ F.sd.wF r s (lab v) (lab w) = true))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hrs, hr0, hr1, hr2⟩, ⟨hs0, hs1, hs2⟩, ⟨h01, h02⟩, h12, -⟩ := hnd
  have hr : ∀ i, r ≠ lab i := by
    intro i
    rcases i with ⟨_ | _ | _ | i, hi⟩
    · exact hr0
    · exact hr1
    · exact hr2
    · omega
  have hs : ∀ i, s ≠ lab i := by
    intro i
    rcases i with ⟨_ | _ | _ | i, hi⟩
    · exact hs0
    · exact hs1
    · exact hs2
    · omega
  have hl : ∀ i j, i ≠ j → lab i ≠ lab j := by
    intro i j hij
    rcases i with ⟨_ | _ | _ | i, hi⟩ <;> rcases j with ⟨_ | _ | _ | j, hj⟩
    all_goals first
      | omega
      | exact absurd rfl hij
      | exact h01
      | exact h02
      | exact h12
      | exact Ne.symm h01
      | exact Ne.symm h02
      | exact Ne.symm h12
  refine ⟨fun i => Chart.ch F r s (lab i), fun i => Chart.ca F r s (lab i),
    fun i => Chart.sg F r s * Chart.ch F s r (lab i),
    fun i => Chart.sg F r s * Chart.ca F s r (lab i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact Chart.ch_hyp F hrs (hr v) (hs v)
  · intro v
    exact Chart.H_hyp F hrs (hr v) (hs v)
  · intro v w hvw
    exact Chart.ca_ne F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw)
  · intro v w hvw
    exact Chart.A_ne F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw)
  · intro v
    exact Chart.iff_of_decide (Chart.h_sign F hrs (hr v) (hs v))
  · intro v
    exact Chart.iff_of_decide (Chart.H_sign F hrs (hr v) (hs v))
  · intro v w hvw
    exact Chart.iff_of_decide (Chart.a_sign F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw))
  · intro v w hvw
    exact Chart.iff_of_decide (Chart.A_sign F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw))
  · intro v w hvw
    have hw := Chart.w_sign F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw)
    simp only [wval]
    rw [Chart.w_eq F hrs (hr v) (hr w) (hs v) (hs w) (hl v w hvw)]
    exact ⟨hw.1, Chart.iff_of_decide hw.2⟩

/-- The five-line obstruction (paper, equation `forbidden`). -/
theorem UFam.sd_forb (F : UFam) : F.sd.Forb := by
  intro r s i j k hnd
  have hnd' : [r, s, (![i, j, k] : Fin 3 → Fin 8) 0, (![i, j, k] : Fin 3 → Fin 8) 1,
      (![i, j, k] : Fin 3 → Fin 8) 2].Nodup := hnd
  obtain ⟨h, a, H, A, hh, hH, ha, hA, sh, sH, sa, sA, sw⟩ := F.chart r s ![i, j, k] hnd'
  intro hpat
  exact obstruction_core h a H A hh hH ha hA
    (fun v => F.sd.hF r s ((![i, j, k] : Fin 3 → Fin 8) v))
    (fun v => F.sd.HF r s ((![i, j, k] : Fin 3 → Fin 8) v))
    (fun v w => F.sd.aF r s ((![i, j, k] : Fin 3 → Fin 8) v) ((![i, j, k] : Fin 3 → Fin 8) w))
    (fun v w => F.sd.AF r s ((![i, j, k] : Fin 3 → Fin 8) v) ((![i, j, k] : Fin 3 → Fin 8) w))
    (fun v w => F.sd.wF r s ((![i, j, k] : Fin 3 → Fin 8) v) ((![i, j, k] : Fin 3 → Fin 8) w))
    sh sH sa sA sw hpat

end Results.EightEquidistantLines
