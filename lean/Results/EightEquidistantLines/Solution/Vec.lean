import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Coordinate vectors in ℝ³

A minimal vector library with explicit components, so that all vector identities are `ring`
identities.  `V3` is a triple of reals; `Bridge.lean` identifies it with the points of `E3 = Fin 3 → ℝ`.

* `dot`, `cross`, `det` (`det a b c = a · (b × c)`), `norm2 a = a · a`.
-/

namespace Results.EightEquidistantLines

/-- A vector of `ℝ³` given by its three coordinates. -/
@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace V3

instance : Zero V3 := ⟨⟨0, 0, 0⟩⟩
instance : Add V3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub V3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg V3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩
instance : SMul ℝ V3 := ⟨fun c a => ⟨c * a.x, c * a.y, c * a.z⟩⟩

@[simp] theorem zero_x : (0 : V3).x = 0 := rfl
@[simp] theorem zero_y : (0 : V3).y = 0 := rfl
@[simp] theorem zero_z : (0 : V3).z = 0 := rfl
@[simp] theorem add_x (a b : V3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : V3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : V3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : V3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : V3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : V3) : (a - b).z = a.z - b.z := rfl
@[simp] theorem neg_x (a : V3) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : V3) : (-a).y = -a.y := rfl
@[simp] theorem neg_z (a : V3) : (-a).z = -a.z := rfl
@[simp] theorem smul_x (c : ℝ) (a : V3) : (c • a).x = c * a.x := rfl
@[simp] theorem smul_y (c : ℝ) (a : V3) : (c • a).y = c * a.y := rfl
@[simp] theorem smul_z (c : ℝ) (a : V3) : (c • a).z = c * a.z := rfl

/-- Standard inner product. -/
def dot (a b : V3) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

/-- Cross product. -/
def cross (a b : V3) : V3 := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

/-- Determinant (scalar triple product) `a · (b × c)`. -/
def det (a b c : V3) : ℝ := dot a (cross b c)

/-- Squared Euclidean norm. -/
def norm2 (a : V3) : ℝ := dot a a

@[simp] theorem cross_x (a b : V3) : (cross a b).x = a.y * b.z - a.z * b.y := rfl
@[simp] theorem cross_y (a b : V3) : (cross a b).y = a.z * b.x - a.x * b.z := rfl
@[simp] theorem cross_z (a b : V3) : (cross a b).z = a.x * b.y - a.y * b.x := rfl

theorem dot_comm (a b : V3) : dot a b = dot b a := by simp only [dot]; ring
theorem dot_add_right (a b c : V3) : dot a (b + c) = dot a b + dot a c := by simp only [dot, add_x, add_y, add_z]; ring
theorem dot_sub_right (a b c : V3) : dot a (b - c) = dot a b - dot a c := by simp only [dot, sub_x, sub_y, sub_z]; ring
theorem dot_smul_right (a : V3) (c : ℝ) (b : V3) : dot a (c • b) = c * dot a b := by simp only [dot, smul_x, smul_y, smul_z]; ring
theorem dot_neg_right (a b : V3) : dot a (-b) = -dot a b := by simp only [dot, neg_x, neg_y, neg_z]; ring
theorem add_dot (a b c : V3) : dot (a + b) c = dot a c + dot b c := by simp only [dot, add_x, add_y, add_z]; ring
theorem sub_dot (a b c : V3) : dot (a - b) c = dot a c - dot b c := by simp only [dot, sub_x, sub_y, sub_z]; ring
theorem smul_dot (c : ℝ) (a b : V3) : dot (c • a) b = c * dot a b := by simp only [dot, smul_x, smul_y, smul_z]; ring

theorem norm2_nonneg (a : V3) : 0 ≤ norm2 a := by
  simp only [norm2, dot]; nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]

theorem norm2_eq_zero_iff (a : V3) : norm2 a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simp only [norm2, dot] at h
    have hx : a.x = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
    have hy : a.y = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
    have hz : a.z = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
    ext <;> simp [hx, hy, hz]
  · intro h; subst h; simp [norm2, dot]

theorem cross_anticomm (a b : V3) : cross a b = -cross b a := by ext <;> simp <;> ring
theorem cross_self (a : V3) : cross a a = 0 := by ext <;> simp <;> ring
theorem cross_add_right (a b c : V3) : cross a (b + c) = cross a b + cross a c := by ext <;> simp <;> ring
theorem cross_sub_right (a b c : V3) : cross a (b - c) = cross a b - cross a c := by ext <;> simp <;> ring
theorem cross_smul_right (a : V3) (c : ℝ) (b : V3) : cross a (c • b) = c • cross a b := by ext <;> simp <;> ring
theorem add_cross (a b c : V3) : cross (a + b) c = cross a c + cross b c := by ext <;> simp <;> ring
theorem smul_cross (c : ℝ) (a b : V3) : cross (c • a) b = c • cross a b := by ext <;> simp <;> ring

theorem dot_cross_self_left (a b : V3) : dot a (cross a b) = 0 := by simp only [dot, cross_x, cross_y, cross_z]; ring
theorem dot_cross_self_right (a b : V3) : dot b (cross a b) = 0 := by simp only [dot, cross_x, cross_y, cross_z]; ring

/-- Binet–Cauchy / Lagrange identity. -/
theorem cross_dot_cross (a b c d : V3) :
    dot (cross a b) (cross c d) = dot a c * dot b d - dot a d * dot b c := by
  simp only [dot, cross_x, cross_y, cross_z]; ring

theorem norm2_cross (a b : V3) : norm2 (cross a b) = norm2 a * norm2 b - dot a b ^ 2 := by
  simp only [norm2]; rw [cross_dot_cross]; simp only [dot_comm b a]; ring

/-- Vector triple product. -/
theorem cross_cross (a b c : V3) : cross a (cross b c) = dot a c • b - dot a b • c := by
  ext <;> simp [dot] <;> try ring

theorem det_eq (a b c : V3) :
    det a b c = a.x * (b.y * c.z - b.z * c.y) + a.y * (b.z * c.x - b.x * c.z) + a.z * (b.x * c.y - b.y * c.x) := by
  simp only [det, dot, cross_x, cross_y, cross_z]

theorem det_swap12 (a b c : V3) : det b a c = -det a b c := by simp only [det_eq]; ring
theorem det_swap23 (a b c : V3) : det a c b = -det a b c := by simp only [det_eq]; ring
theorem det_cyc (a b c : V3) : det b c a = det a b c := by simp only [det_eq]; ring
theorem det_self_left (a c : V3) : det a a c = 0 := by simp only [det_eq]; ring
theorem det_self_mid (a b : V3) : det a b a = 0 := by simp only [det_eq]; ring
theorem det_self_right (a b : V3) : det a b b = 0 := by simp only [det_eq]; ring
theorem det_eq_dot_cross_left (a b c : V3) : det a b c = dot (cross a b) c := by simp only [det_eq, dot, cross_x, cross_y, cross_z]; ring

/-- Gram determinant identity. -/
theorem det_sq (a b c : V3) :
    det a b c ^ 2 = norm2 a * norm2 b * norm2 c + 2 * dot a b * dot b c * dot c a
      - norm2 a * dot b c ^ 2 - norm2 b * dot c a ^ 2 - norm2 c * dot a b ^ 2 := by
  simp only [det_eq, norm2, dot]; ring

end V3

end Results.EightEquidistantLines
