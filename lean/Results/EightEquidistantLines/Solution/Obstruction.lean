import Results.EightEquidistantLines.Solution.Spec
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The five-line obstruction in sign form (paper, Section 5)

On a hyperbola `h² - a² = 1` put `α = h + a`; then `h = (α + α⁻¹)/2`, `a = (α - α⁻¹)/2`, and the divided
difference of `h` against `a` between two points is `(α_iα_j - 1)/(α_iα_j + 1)`, strictly increasing in
`α_iα_j > 0`.  This replaces the secant-monotonicity lemma of the paper (Lemma 5.1) by sign arithmetic.

`wval h a H A v w = 1 + (h_w - h_v)/(a_w - a_v) + (H_w - H_v)/(A_w - A_v)` is the paper's `w_{vw}` of
equation (4.3).  `obstruction_core` is Proposition 5.2 in sign form, for the three points `0,1,2`
(= the labels `i, j, k`).
-/

namespace Results.EightEquidistantLines

/-- The paper's `w_{vw} = 1 + (h_w - h_v)/(a_w - a_v) + (H_w - H_v)/(A_w - A_v)`. -/
noncomputable def wval (h a H A : Fin 3 → ℝ) (v w : Fin 3) : ℝ :=
  1 + (h w - h v) / (a w - a v) + (H w - H v) / (A w - A v)

namespace Obstruction

/-! ### One hyperbola -/

/-- On the hyperbola `h² - a² = 1`: `(h + a) h = ((h + a)² + 1)/2 > 0`, so `h + a` has the sign of `h`. -/
theorem alpha_mul_pos {h a : ℝ} (e : h ^ 2 - a ^ 2 = 1) : 0 < (h + a) * h := by
  have key : (h + a) * h = ((h + a) ^ 2 + 1) / 2 := by linear_combination (1 / 2 : ℝ) * e
  rw [key]
  positivity

/-- Two points of the hyperbola on the same sheet have `α α' > 0` for `α = h + a`. -/
theorem alpha_prod_pos {h a h' a' : ℝ} (e : h ^ 2 - a ^ 2 = 1) (e' : h' ^ 2 - a' ^ 2 = 1)
    (s : 0 < h * h') : 0 < (h + a) * (h' + a') := by
  have h1 := mul_pos (alpha_mul_pos e) (alpha_mul_pos e')
  have h2 : 0 < ((h + a) * (h' + a')) * (h * h') := by
    have key : ((h + a) * (h' + a')) * (h * h') = ((h + a) * h) * ((h' + a') * h') := by ring
    rw [key]
    exact h1
  exact (mul_pos_iff_of_pos_right s).mp h2

/-- The divided difference of `h` against `a` is `(P - 1)/(P + 1)` with `P = α α'`. -/
theorem div_diff {h a h' a' : ℝ} (e : h ^ 2 - a ^ 2 = 1) (e' : h' ^ 2 - a' ^ 2 = 1)
    (hP : 0 < (h + a) * (h' + a')) (hd : a' - a ≠ 0) :
    (h' - h) / (a' - a) = ((h + a) * (h' + a') - 1) / ((h + a) * (h' + a') + 1) := by
  have hP1 : (h + a) * (h' + a') + 1 ≠ 0 := by positivity
  rw [div_eq_div_iff hd hP1]
  linear_combination (h + a) * e' - (h' + a') * e

/-- `2 P (a' - a) = (α' - α)(P + 1)` with `P = α α'`. -/
theorem a_diff {h a h' a' : ℝ} (e : h ^ 2 - a ^ 2 = 1) (e' : h' ^ 2 - a' ^ 2 = 1) :
    2 * ((h + a) * (h' + a')) * (a' - a) =
      ((h' + a') - (h + a)) * ((h + a) * (h' + a') + 1) := by
  linear_combination (h' + a') * e - (h + a) * e'

/-- `a' - a` has the sign of `α' - α` on a common sheet. -/
theorem alpha_diff_mul_pos {h a h' a' : ℝ} (e : h ^ 2 - a ^ 2 = 1) (e' : h' ^ 2 - a' ^ 2 = 1)
    (hP : 0 < (h + a) * (h' + a')) (hd : a' - a ≠ 0) :
    0 < ((h' + a') - (h + a)) * (a' - a) := by
  have key := a_diff e e'
  have h2P : 0 < 2 * ((h + a) * (h' + a')) := by positivity
  have hα : (h' + a') - (h + a) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at key
    exact hd ((mul_eq_zero.mp key).resolve_left h2P.ne')
  have h1 : 0 < ((h' + a') - (h + a)) * (a' - a) * (2 * ((h + a) * (h' + a'))) := by
    have key2 : ((h' + a') - (h + a)) * (a' - a) * (2 * ((h + a) * (h' + a')))
        = ((h' + a') - (h + a)) ^ 2 * ((h + a) * (h' + a') + 1) := by
      linear_combination ((h' + a') - (h + a)) * key
    rw [key2]
    positivity
  exact (mul_pos_iff_of_pos_right h2P).mp h1

/-- One side (`h, a` or `H, A`) of the obstruction: on a common sheet the difference of the two
secant slopes from the point `0` has the sign of `h₀ (a₂ - a₁)`. -/
theorem side_real {h0 a0 h1 a1 h2 a2 : ℝ}
    (e0 : h0 ^ 2 - a0 ^ 2 = 1) (e1 : h1 ^ 2 - a1 ^ 2 = 1) (e2 : h2 ^ 2 - a2 ^ 2 = 1)
    (n01 : a1 - a0 ≠ 0) (n02 : a2 - a0 ≠ 0) (n12 : a2 - a1 ≠ 0)
    (s01 : 0 < h0 * h1) (s02 : 0 < h0 * h2) (s12 : 0 < h1 * h2) :
    0 < ((h2 - h0) / (a2 - a0) - (h1 - h0) / (a1 - a0)) * (h0 * (a2 - a1)) := by
  have P01 := alpha_prod_pos e0 e1 s01
  have P02 := alpha_prod_pos e0 e2 s02
  have P12 := alpha_prod_pos e1 e2 s12
  rw [div_diff e0 e2 P02 n02, div_diff e0 e1 P01 n01]
  have k0 := alpha_mul_pos e0
  have k12 := alpha_diff_mul_pos e1 e2 P12 n12
  have d1 : (h0 + a0) * (h2 + a2) + 1 ≠ 0 := by positivity
  have d2 : (h0 + a0) * (h1 + a1) + 1 ≠ 0 := by positivity
  have hden : 0 < ((h0 + a0) * (h2 + a2) + 1) * ((h0 + a0) * (h1 + a1) + 1) := by positivity
  have key : (((h0 + a0) * (h2 + a2) - 1) / ((h0 + a0) * (h2 + a2) + 1)
        - ((h0 + a0) * (h1 + a1) - 1) / ((h0 + a0) * (h1 + a1) + 1)) * (h0 * (a2 - a1))
      = 2 * (((h0 + a0) * h0) * (((h2 + a2) - (h1 + a1)) * (a2 - a1)))
          / (((h0 + a0) * (h2 + a2) + 1) * ((h0 + a0) * (h1 + a1) + 1)) := by
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos two_pos (mul_pos k0 k12)) hden

/-! ### Sign bookkeeping -/

/-- A nonzero real together with its negativity flag. -/
theorem sign_of_flag {s : ℝ} {b : Bool} (hs0 : s ≠ 0) (hs : s < 0 ↔ b = true) :
    (b = true ∧ s < 0) ∨ (b = false ∧ 0 < s) := by
  cases b
  · right
    refine ⟨rfl, ?_⟩
    have hn : ¬ s < 0 := fun h => by simpa using hs.mp h
    exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hs0)
  · exact Or.inl ⟨rfl, hs.mpr rfl⟩

/-- The flag of a product is the exclusive or of the flags. -/
theorem mul_neg_iff_xor {s t : ℝ} {b c : Bool} (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hs : s < 0 ↔ b = true) (ht : t < 0 ↔ c = true) : s * t < 0 ↔ (b ^^ c) = true := by
  rcases sign_of_flag hs0 hs with ⟨hb, h1⟩ | ⟨hb, h1⟩ <;>
    rcases sign_of_flag ht0 ht with ⟨hc, h2⟩ | ⟨hc, h2⟩ <;> subst hb <;> subst hc
  · have hp := mul_pos_of_neg_of_neg h1 h2
    simp only [Bool.xor_self]
    exact ⟨fun h => absurd h (not_lt.mpr hp.le), fun h => absurd h (by simp)⟩
  · have hn := mul_neg_of_neg_of_pos h1 h2
    simp only [Bool.true_xor, Bool.not_false]
    exact ⟨fun _ => trivial, fun _ => hn⟩
  · have hn := mul_neg_of_pos_of_neg h1 h2
    simp only [Bool.false_xor]
    exact ⟨fun _ => trivial, fun _ => hn⟩
  · have hp := mul_pos h1 h2
    simp only [Bool.xor_self]
    exact ⟨fun h => absurd h (not_lt.mpr hp.le), fun h => absurd h (by simp)⟩

/-- The final sign contradiction. -/
theorem final_step {η f1 f2 : Bool} {W1 W2 dD dE x y : ℝ}
    (hdx : 0 < dD * x) (hey : 0 < dE * y)
    (hx : x < 0 ↔ η = true) (hy : y < 0 ↔ η = true)
    (hW : W2 - W1 = dD + dE)
    (hw1 : W1 ≠ 0 ∧ (W1 < 0 ↔ f1 = true)) (hw2 : W2 ≠ 0 ∧ (W2 < 0 ↔ f2 = true))
    (e6 : η = f1) (e7 : f1 = !f2) : False := by
  obtain ⟨hW1, hW1'⟩ := hw1
  obtain ⟨hW2, hW2'⟩ := hw2
  cases η
  · -- `η = false`: `x, y > 0`, so `dD, dE > 0`; `W1 > 0` and `W2 < 0`
    subst e6
    cases f2
    · simp at e7
    · have hx0 : x ≠ 0 := fun h => by simp [h] at hdx
      have hy0 : y ≠ 0 := fun h => by simp [h] at hey
      rcases sign_of_flag hx0 hx with ⟨h, _⟩ | ⟨_, hxp⟩
      · simp at h
      rcases sign_of_flag hy0 hy with ⟨h, _⟩ | ⟨_, hyp⟩
      · simp at h
      have hdD : 0 < dD := pos_of_mul_pos_left hdx hxp.le
      have hdE : 0 < dE := pos_of_mul_pos_left hey hyp.le
      rcases sign_of_flag hW1 hW1' with ⟨h, _⟩ | ⟨_, hw1p⟩
      · simp at h
      have hw2n : W2 < 0 := hW2'.mpr rfl
      linarith
  · -- `η = true`: `x, y < 0`, so `dD, dE < 0`; `W1 < 0` and `W2 > 0`
    subst e6
    cases f2
    · have hx' : x < 0 := hx.mpr rfl
      have hy' : y < 0 := hy.mpr rfl
      have hdD : dD < 0 := neg_of_mul_pos_left hdx hx'.le
      have hdE : dE < 0 := neg_of_mul_pos_left hey hy'.le
      have hw1n : W1 < 0 := hW1'.mpr rfl
      rcases sign_of_flag hW2 hW2' with ⟨h, _⟩ | ⟨_, hw2p⟩
      · simp at h
      linarith
    · simp at e7

/-- A point of the hyperbola has `h ≠ 0`. -/
theorem ne_zero_of_hyp {h a : ℝ} (e : h ^ 2 - a ^ 2 = 1) : h ≠ 0 := by
  intro hz
  rw [hz] at e
  linarith [sq_nonneg a]

/-- Two points whose negativity flags agree lie on the same sheet. -/
theorem sheet {h a h' a' : ℝ} {b b' : Bool} (e : h ^ 2 - a ^ 2 = 1) (e' : h' ^ 2 - a' ^ 2 = 1)
    (hs : h < 0 ↔ b = true) (hs' : h' < 0 ↔ b' = true) (hb : b = b') : 0 < h * h' := by
  rcases sign_of_flag (ne_zero_of_hyp e) hs with ⟨hb1, h1⟩ | ⟨hb1, h1⟩ <;>
    rcases sign_of_flag (ne_zero_of_hyp e') hs' with ⟨hb2, h2⟩ | ⟨hb2, h2⟩
  · exact mul_pos_of_neg_of_neg h1 h2
  · exact absurd hb (by simp [hb1, hb2])
  · exact absurd hb (by simp [hb1, hb2])
  · exact mul_pos h1 h2

end Obstruction

/-- Proposition 5.2 in sign form. -/
theorem obstruction_core (h a H A : Fin 3 → ℝ)
    (hh : ∀ v, h v ^ 2 - a v ^ 2 = 1) (hH : ∀ v, H v ^ 2 - A v ^ 2 = 1)
    (ha : ∀ v w, v ≠ w → a v ≠ a w) (hA : ∀ v w, v ≠ w → A v ≠ A w)
    (fh fH : Fin 3 → Bool) (fa fA fw : Fin 3 → Fin 3 → Bool)
    (sh : ∀ v, (h v < 0 ↔ fh v = true)) (sH : ∀ v, (H v < 0 ↔ fH v = true))
    (sa : ∀ v w, v ≠ w → (a w - a v < 0 ↔ fa v w = true))
    (sA : ∀ v w, v ≠ w → (A w - A v < 0 ↔ fA v w = true))
    (sw : ∀ v w, v ≠ w → (wval h a H A v w ≠ 0 ∧ (wval h a H A v w < 0 ↔ fw v w = true))) :
    ¬ (fh 0 = fh 1 ∧ fh 1 = fh 2 ∧ fH 0 = fH 1 ∧ fH 1 = fH 2 ∧
       (fh 0 ^^ fa 1 2) = (fH 0 ^^ fA 1 2) ∧ (fH 0 ^^ fA 1 2) = fw 0 1 ∧ fw 0 1 = !fw 0 2) := by
  rintro ⟨e1, e2, e3, e4, e5, e6, e7⟩
  -- all three points of each hyperbola lie on one sheet
  have s01 := Obstruction.sheet (hh 0) (hh 1) (sh 0) (sh 1) e1
  have s02 := Obstruction.sheet (hh 0) (hh 2) (sh 0) (sh 2) (e1.trans e2)
  have s12 := Obstruction.sheet (hh 1) (hh 2) (sh 1) (sh 2) e2
  have t01 := Obstruction.sheet (hH 0) (hH 1) (sH 0) (sH 1) e3
  have t02 := Obstruction.sheet (hH 0) (hH 2) (sH 0) (sH 2) (e3.trans e4)
  have t12 := Obstruction.sheet (hH 1) (hH 2) (sH 1) (sH 2) e4
  have n01 : a 1 - a 0 ≠ 0 := sub_ne_zero.mpr (ha 1 0 (by decide))
  have n02 : a 2 - a 0 ≠ 0 := sub_ne_zero.mpr (ha 2 0 (by decide))
  have n12 : a 2 - a 1 ≠ 0 := sub_ne_zero.mpr (ha 2 1 (by decide))
  have m01 : A 1 - A 0 ≠ 0 := sub_ne_zero.mpr (hA 1 0 (by decide))
  have m02 : A 2 - A 0 ≠ 0 := sub_ne_zero.mpr (hA 2 0 (by decide))
  have m12 : A 2 - A 1 ≠ 0 := sub_ne_zero.mpr (hA 2 1 (by decide))
  -- the secant-slope differences have the sign of `h 0 * (a 2 - a 1)`, resp. `H 0 * (A 2 - A 1)`
  have dD := Obstruction.side_real (hh 0) (hh 1) (hh 2) n01 n02 n12 s01 s02 s12
  have dE := Obstruction.side_real (hH 0) (hH 1) (hH 2) m01 m02 m12 t01 t02 t12
  have hx : h 0 * (a 2 - a 1) < 0 ↔ (fH 0 ^^ fA 1 2) = true := by
    rw [← e5]
    exact Obstruction.mul_neg_iff_xor (Obstruction.ne_zero_of_hyp (hh 0)) n12 (sh 0)
      (sa 1 2 (by decide))
  have hy : H 0 * (A 2 - A 1) < 0 ↔ (fH 0 ^^ fA 1 2) = true :=
    Obstruction.mul_neg_iff_xor (Obstruction.ne_zero_of_hyp (hH 0)) m12 (sH 0)
      (sA 1 2 (by decide))
  have hW : wval h a H A 0 2 - wval h a H A 0 1 =
      ((h 2 - h 0) / (a 2 - a 0) - (h 1 - h 0) / (a 1 - a 0)) +
        ((H 2 - H 0) / (A 2 - A 0) - (H 1 - H 0) / (A 1 - A 0)) := by
    unfold wval
    ring
  exact Obstruction.final_step dD dE hx hy hW (sw 0 1 (by decide)) (sw 0 2 (by decide)) e6 e7

end Results.EightEquidistantLines
