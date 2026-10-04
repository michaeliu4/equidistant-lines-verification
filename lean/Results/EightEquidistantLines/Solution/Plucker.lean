import Results.EightEquidistantLines.Solution.Signs

/-!
# Three-term Grassmann–Plücker relations for the direction signs

The determinants of five vectors of `ℝ³` satisfy
`det(a,b,c) det(a,d,e) - det(a,b,d) det(a,c,e) + det(a,b,e) det(a,c,d) = 0`; as all the determinants
of distinct directions are non-zero, the three terms are not all of one sign.
-/

namespace Results.EightEquidistantLines

open V3

namespace Plucker

/-- The three-term Grassmann–Plücker identity for five vectors of `ℝ³` with pivot `a`. -/
theorem three_term (a b c d e : V3) :
    det a b c * det a d e - det a b d * det a c e + det a b e * det a c d = 0 := by
  simp only [det_eq]; ring

/-- Negation flips the negativity flag of a non-zero real (same statement as `Signs.flag_neg`,
repeated so that this file only depends on the public interface of `Signs`). -/
theorem flag_neg {x : ℝ} (hx : x ≠ 0) : decide (-x < 0) = !decide (x < 0) := by
  rcases lt_or_gt_of_ne hx with p | p
  · have : ¬ (-x < 0) := not_lt.2 (neg_nonneg.2 p.le)
    simp [p, this]
  · have : -x < 0 := neg_lt_zero.2 p
    simp [this, not_lt.2 p.le]

/-- Products of non-zero reals multiply signs, i.e. exclusive-or the negativity flags. -/
theorem flag_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (x * y < 0) = (decide (x < 0) ^^ decide (y < 0)) := by
  rcases lt_or_gt_of_ne hx with px | px <;> rcases lt_or_gt_of_ne hy with py | py
  · have : ¬ (x * y < 0) := not_lt.2 (mul_pos_of_neg_of_neg px py).le
    simp [px, py, this]
  · have : x * y < 0 := mul_neg_of_neg_of_pos px py
    simp [px, not_lt.2 py.le, this]
  · have : x * y < 0 := mul_neg_of_pos_of_neg px py
    simp [py, not_lt.2 px.le, this]
  · have : ¬ (x * y < 0) := not_lt.2 (mul_pos px py).le
    simp [not_lt.2 px.le, not_lt.2 py.le, this]

/-- Three non-zero reals with sum zero cannot all have the same sign. -/
theorem flags_not_all_eq {t₁ t₂ t₃ : ℝ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0)
    (hsum : t₁ + t₂ + t₃ = 0) :
    ¬ (decide (t₁ < 0) = decide (t₂ < 0) ∧ decide (t₂ < 0) = decide (t₃ < 0)) := by
  rintro ⟨e₁₂, e₂₃⟩
  have i₁₂ : t₁ < 0 ↔ t₂ < 0 := decide_eq_decide.1 e₁₂
  have i₂₃ : t₂ < 0 ↔ t₃ < 0 := decide_eq_decide.1 e₂₃
  rcases lt_or_gt_of_ne h₁ with p₁ | p₁
  · have p₂ := i₁₂.1 p₁
    have p₃ := i₂₃.1 p₂
    linarith
  · have p₂ : 0 < t₂ :=
      lt_of_le_of_ne (not_lt.1 fun h => absurd p₁ (not_lt.2 (i₁₂.2 h).le)) h₂.symm
    have p₃ : 0 < t₃ :=
      lt_of_le_of_ne (not_lt.1 fun h => absurd p₂ (not_lt.2 (i₂₃.2 h).le)) h₃.symm
    linarith

/-- A duplicate-free list of five labels yields the ten pairwise inequalities. -/
theorem nodup5 {a b c d e : Fin 8} (h : [a, b, c, d, e].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  simp [List.nodup_cons] at h
  obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩ := h
  exact ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩

end Plucker

theorem UFam.sd_gp (F : UFam) : F.sd.GP := by
  intro a b c d e h
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := Plucker.nodup5 h
  -- the six determinants of the relation with pivot `a`
  have hA := F.det_ne hab hac hbc
  have hB := F.det_ne had hae hde
  have hC := F.det_ne hab had hbd
  have hD := F.det_ne hac hae hce
  have hE := F.det_ne hab hae hbe
  have hG := F.det_ne hac had hcd
  -- flags of the three terms `A * B`, `-(C * D)`, `E * G`
  have e₁ : (decide (det (F.u a) (F.u b) (F.u c) < 0) ^^ decide (det (F.u a) (F.u d) (F.u e) < 0)) =
      decide (det (F.u a) (F.u b) (F.u c) * det (F.u a) (F.u d) (F.u e) < 0) :=
    (Plucker.flag_mul hA hB).symm
  have e₂ : (decide (det (F.u a) (F.u b) (F.u d) < 0) ^^ decide (det (F.u a) (F.u c) (F.u e) < 0) ^^
      true) = decide (-(det (F.u a) (F.u b) (F.u d) * det (F.u a) (F.u c) (F.u e)) < 0) := by
    rw [Plucker.flag_neg (mul_ne_zero hC hD), Plucker.flag_mul hC hD, Bool.xor_true]
  have e₃ : (decide (det (F.u a) (F.u b) (F.u e) < 0) ^^ decide (det (F.u a) (F.u c) (F.u d) < 0)) =
      decide (det (F.u a) (F.u b) (F.u e) * det (F.u a) (F.u c) (F.u d) < 0) :=
    (Plucker.flag_mul hE hG).symm
  have hsum : det (F.u a) (F.u b) (F.u c) * det (F.u a) (F.u d) (F.u e) +
      -(det (F.u a) (F.u b) (F.u d) * det (F.u a) (F.u c) (F.u e)) +
      det (F.u a) (F.u b) (F.u e) * det (F.u a) (F.u c) (F.u d) = 0 := by
    have := Plucker.three_term (F.u a) (F.u b) (F.u c) (F.u d) (F.u e)
    linarith
  simp only [SD.GPinst, UFam.sd_neg3]
  rw [e₁, e₂, e₃]
  exact Plucker.flags_not_all_eq (mul_ne_zero hA hB) (neg_ne_zero.2 (mul_ne_zero hC hD))
    (mul_ne_zero hE hG) hsum

end Results.EightEquidistantLines
