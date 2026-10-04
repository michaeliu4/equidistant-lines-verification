import Results.EightEquidistantLines.Solution.LineDist
import Results.EightEquidistantLines.Solution.Spec

/-!
# Families of eight unit-distance lines

`UFam` is a family of eight lines `p_i + ℝ u_i` with unit direction vectors and pairwise distance one,
with chosen anchors and oriented directions.  `UFam.T F i j = (p_i - p_j) · (u_i × u_j)` is the
paper's `T_{ij}`, and `UFam.sd F` is its sign data: `neg3 a b c` is the sign of `det(u_a,u_b,u_c)`
and `neg2 a b` the sign of `T_{ab}`.
-/

namespace Results.EightEquidistantLines

open V3

/-- Eight lines `p i + ℝ (u i)` with unit directions and pairwise distance `1`. -/
structure UFam where
  p : Fin 8 → V3
  u : Fin 8 → V3
  unit : ∀ i, norm2 (u i) = 1
  dist1 : ∀ i j, i ≠ j → lineDist3 (p i) (u i) (p j) (u j) = 1

namespace UFam

/-- The signed distance numerator `T_{ij} = (p_i - p_j) · (u_i × u_j)`. -/
def T (F : UFam) (i j : Fin 8) : ℝ := det (F.p i - F.p j) (F.u i) (F.u j)

/-- Sign data of the family (`true` means negative). -/
noncomputable def sd (F : UFam) : SD where
  neg3 a b c := decide (det (F.u a) (F.u b) (F.u c) < 0)
  neg2 a b := decide (F.T a b < 0)

@[simp] theorem sd_neg3 (F : UFam) (a b c : Fin 8) :
    F.sd.neg3 a b c = decide (det (F.u a) (F.u b) (F.u c) < 0) := rfl

@[simp] theorem sd_neg2 (F : UFam) (a b : Fin 8) : F.sd.neg2 a b = decide (F.T a b < 0) := rfl

theorem T_symm (F : UFam) (i j : Fin 8) : F.T j i = F.T i j := by
  simp only [T, det_eq, sub_x, sub_y, sub_z]; ring

end UFam

end Results.EightEquidistantLines
