import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Basic

/-!
# Sign data of eight oriented lines and the local constraints on it

`SD` is the *sign data* of an oriented line family, in "negativity flag" form (`true` = negative):

* `neg3 a b c` : the sign of the determinant `det(u_a, u_b, u_c)` of the three oriented directions
  (the chirotope value `χ_{abc}`);
* `neg2 a b` : the sign of the signed distance numerator `T_{ab} = (p_a - p_b) · (u_a × u_b)`
  (the paper's `ε_{ab}`).

The local constraints below come from the paper: the three-term Grassmann–Plücker relations (`GP`;
the paper only invokes them through the chirotope axioms of its Section 6.1, here they are proved from the
geometry), the four-line circuit condition of Lemma 3.1 (`Circ`, over all orderings of the four labels)
and the five-line obstruction of Section 5 (`Forb`, the sign-only form (5.1)).  Products of signs become
exclusive-or of flags.  `Valid8 D` bundles them; the purely combinatorial theorem `Kfinal.no_valid8` shows
that no `D` is valid (this replaces the paper's use of Finschi's catalogue), and the geometric modules show
that the sign data of eight unit-distance lines is valid.
-/

namespace Results.EightEquidistantLines

/-- Sign data on eight labels (`true` means negative). -/
structure SD where
  neg3 : Fin 8 → Fin 8 → Fin 8 → Bool
  neg2 : Fin 8 → Fin 8 → Bool

namespace SD

/-- `neg3` is alternating on distinct labels and `neg2` is symmetric. -/
def Wf (D : SD) : Prop :=
  (∀ a b c : Fin 8, [a, b, c].Nodup → D.neg3 b a c = !D.neg3 a b c) ∧
  (∀ a b c : Fin 8, [a, b, c].Nodup → D.neg3 a c b = !D.neg3 a b c) ∧
  (∀ a b : Fin 8, D.neg2 b a = D.neg2 a b)

/-- Three-term Grassmann–Plücker relation with pivot `a`: the three terms
`χ_{abc}χ_{ade}`, `-χ_{abd}χ_{ace}`, `χ_{abe}χ_{acd}` are not all equal. -/
def GPinst (D : SD) (a b c d e : Fin 8) : Prop :=
  ¬ ((D.neg3 a b c ^^ D.neg3 a d e) = (D.neg3 a b d ^^ D.neg3 a c e ^^ true) ∧
     (D.neg3 a b d ^^ D.neg3 a c e ^^ true) = (D.neg3 a b e ^^ D.neg3 a c d))

def GP (D : SD) : Prop := ∀ a b c d e : Fin 8, [a, b, c, d, e].Nodup → D.GPinst a b c d e

/-- Some vertex carries two incident edges whose flags both equal `c`. -/
def twoAt (x y z c : Bool) : Prop := (x = c ∧ y = c) ∨ (x = c ∧ z = c) ∨ (y = c ∧ z = c)

/-- Lemma 3.1 (four-line circuit condition) for the ordered four-tuple `(v0, v1, v2, v3)`:
with `α_k = (-1)^k det(u_{v_0}, .., omit k, .., u_{v_3})` and `σ_{ij} = ε_{v_i v_j} sgn(α_i α_j)`,
neither sign class of the six-edge graph `σ` on `{0,1,2,3}` is a matching (empty counts as matching). -/
def CircInst (D : SD) (v0 v1 v2 v3 : Fin 8) : Prop :=
  let α0 := D.neg3 v1 v2 v3
  let α1 := !D.neg3 v0 v2 v3
  let α2 := D.neg3 v0 v1 v3
  let α3 := !D.neg3 v0 v1 v2
  let s01 := D.neg2 v0 v1 ^^ α0 ^^ α1
  let s02 := D.neg2 v0 v2 ^^ α0 ^^ α2
  let s03 := D.neg2 v0 v3 ^^ α0 ^^ α3
  let s12 := D.neg2 v1 v2 ^^ α1 ^^ α2
  let s13 := D.neg2 v1 v3 ^^ α1 ^^ α3
  let s23 := D.neg2 v2 v3 ^^ α2 ^^ α3
  ∀ c : Bool, twoAt s01 s02 s03 c ∨ twoAt s01 s12 s13 c ∨ twoAt s02 s12 s23 c ∨ twoAt s03 s13 s23 c

def Circ (D : SD) : Prop := ∀ v0 v1 v2 v3 : Fin 8, [v0, v1, v2, v3].Nodup → D.CircInst v0 v1 v2 v3

/-- Flags of the five sign quantities `h*, H*, a*, A*, w*` of the paper's sign-only form of the
five-line obstruction, for base labels `r, s`:
`h*_v = ε_rs ε_rv χ_rsv`, `H*_v = -ε_sv χ_rsv`, `a*_vw = χ_rsv χ_rsw χ_rvw`,
`A*_vw = ε_rs χ_rsv χ_rsw χ_svw`, `w*_vw = -ε_rs ε_vw χ_rsv χ_rsw χ_rvw χ_svw`. -/
def hF (D : SD) (r s v : Fin 8) : Bool := D.neg2 r s ^^ D.neg2 r v ^^ D.neg3 r s v
def HF (D : SD) (r s v : Fin 8) : Bool := true ^^ D.neg2 s v ^^ D.neg3 r s v
def aF (D : SD) (r s v w : Fin 8) : Bool := D.neg3 r s v ^^ D.neg3 r s w ^^ D.neg3 r v w
def AF (D : SD) (r s v w : Fin 8) : Bool := D.neg2 r s ^^ D.neg3 r s v ^^ D.neg3 r s w ^^ D.neg3 s v w
def wF (D : SD) (r s v w : Fin 8) : Bool :=
  true ^^ D.neg2 r s ^^ D.neg2 v w ^^ D.neg3 r s v ^^ D.neg3 r s w ^^ D.neg3 r v w ^^ D.neg3 s v w

/-- The five-line obstruction (equation `forbidden`): the following sign conjunction is impossible
for distinct labels `r, s, i, j, k`:
`h*_i = h*_j = h*_k`, `H*_i = H*_j = H*_k`, `h*_i a*_jk = H*_i A*_jk = w*_ij = -w*_ik`. -/
def ForbInst (D : SD) (r s i j k : Fin 8) : Prop :=
  ¬ (D.hF r s i = D.hF r s j ∧ D.hF r s j = D.hF r s k ∧
     D.HF r s i = D.HF r s j ∧ D.HF r s j = D.HF r s k ∧
     (D.hF r s i ^^ D.aF r s j k) = (D.HF r s i ^^ D.AF r s j k) ∧
     (D.HF r s i ^^ D.AF r s j k) = D.wF r s i j ∧
     D.wF r s i j = !D.wF r s i k)

def Forb (D : SD) : Prop := ∀ r s i j k : Fin 8, [r, s, i, j, k].Nodup → D.ForbInst r s i j k

/-- All local constraints. -/
def Valid8 (D : SD) : Prop := D.Wf ∧ D.GP ∧ D.Circ ∧ D.Forb

end SD

end Results.EightEquidistantLines
