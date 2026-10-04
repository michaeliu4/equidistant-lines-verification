import Results.EightEquidistantLines.Solution.Spec

/-!
# Symmetries of the sign data

A symmetry `w : W` consists of an injective renaming `π` of the labels, reorientation signs `g`
(reversing the direction of line `a` multiplies every `χ` containing `a` and every `ε` at `a` by
`-1`) and a global flip `ν` of the distance signs (a spatial reflection followed by reversing all
directions).  `SD.act w D` is the transformed sign data; the local constraints are invariant:
`Valid8 D → Valid8 (D.act w)`.

The proof is pure Boolean xor algebra: every constraint instance for `D.act w` is the instance for
`D` at the renamed labels (injectivity of `π` keeps the label tuples duplicate free), with all
quantities changed by flags that cancel in the constraint (`g` cancels, `ν` complements `σ`).
-/

namespace Results.EightEquidistantLines

structure W where
  π : Fin 8 → Fin 8
  inj : Function.Injective π
  g : Fin 8 → Bool
  ν : Bool

/-- The transformed sign data: `χ'_{abc} = g_a g_b g_c χ_{π a, π b, π c}`,
`ε'_{ab} = ν g_a g_b ε_{π a, π b}`. -/
def SD.act (w : W) (D : SD) : SD where
  neg3 a b c := w.g a ^^ w.g b ^^ w.g c ^^ D.neg3 (w.π a) (w.π b) (w.π c)
  neg2 a b := w.ν ^^ w.g a ^^ w.g b ^^ D.neg2 (w.π a) (w.π b)

namespace KAct

/-! ### Unfolding lemmas and transport of `Nodup` -/

theorem act_neg3 (w : W) (D : SD) (a b c : Fin 8) :
    (D.act w).neg3 a b c = (w.g a ^^ w.g b ^^ w.g c ^^ D.neg3 (w.π a) (w.π b) (w.π c)) := rfl

theorem act_neg2 (w : W) (D : SD) (a b : Fin 8) :
    (D.act w).neg2 a b = (w.ν ^^ w.g a ^^ w.g b ^^ D.neg2 (w.π a) (w.π b)) := rfl

theorem nd3 (w : W) {a b c : Fin 8} (h : [a, b, c].Nodup) : [w.π a, w.π b, w.π c].Nodup :=
  h.map w.inj

theorem nd4 (w : W) {a b c d : Fin 8} (h : [a, b, c, d].Nodup) :
    [w.π a, w.π b, w.π c, w.π d].Nodup :=
  h.map w.inj

theorem nd5 (w : W) {a b c d e : Fin 8} (h : [a, b, c, d, e].Nodup) :
    [w.π a, w.π b, w.π c, w.π d, w.π e].Nodup :=
  h.map w.inj

/-! ### `Wf` -/

theorem wf_core1 : ∀ ga gb gc x : Bool, (gb ^^ ga ^^ gc ^^ !x) = !(ga ^^ gb ^^ gc ^^ x) := by
  decide

theorem wf_core2 : ∀ ga gb gc x : Bool, (ga ^^ gc ^^ gb ^^ !x) = !(ga ^^ gb ^^ gc ^^ x) := by
  decide

theorem wf_core3 : ∀ ν ga gb x : Bool, (ν ^^ gb ^^ ga ^^ x) = (ν ^^ ga ^^ gb ^^ x) := by
  decide

theorem wf_act (w : W) {D : SD} (h : D.Wf) : (D.act w).Wf := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b c hn => ?_, fun a b c hn => ?_, fun a b => ?_⟩
  · rw [act_neg3, act_neg3, h1 _ _ _ (nd3 w hn)]
    exact wf_core1 _ _ _ _
  · rw [act_neg3, act_neg3, h2 _ _ _ (nd3 w hn)]
    exact wf_core2 _ _ _ _
  · rw [act_neg2, act_neg2, h3 (w.π a) (w.π b)]
    exact wf_core3 _ _ _ _

/-! ### `GP` -/

/-- The three terms of a Grassmann-Plucker instance all gain the common flag
`g b ^^ g c ^^ g d ^^ g e` (the pivot flag `g a` cancels), so the equality between the first two
terms is unchanged. -/
theorem gp_eq1 : ∀ ga gb gc gd ge x1 x2 y1 y2 : Bool,
    (((ga ^^ gb ^^ gc ^^ x1) ^^ (ga ^^ gd ^^ ge ^^ x2)) =
        ((ga ^^ gb ^^ gd ^^ y1) ^^ (ga ^^ gc ^^ ge ^^ y2) ^^ true)) ↔
      ((x1 ^^ x2) = (y1 ^^ y2 ^^ true)) := by
  decide

/-- The equality between the second and the third term is unchanged as well. -/
theorem gp_eq2 : ∀ ga gb gc gd ge y1 y2 z1 z2 : Bool,
    (((ga ^^ gb ^^ gd ^^ y1) ^^ (ga ^^ gc ^^ ge ^^ y2) ^^ true) =
        ((ga ^^ gb ^^ ge ^^ z1) ^^ (ga ^^ gc ^^ gd ^^ z2))) ↔
      ((y1 ^^ y2 ^^ true) = (z1 ^^ z2)) := by
  decide

theorem gp_act (w : W) {D : SD} (h : D.GP) : (D.act w).GP := by
  intro a b c d e hn
  have h1 := h (w.π a) (w.π b) (w.π c) (w.π d) (w.π e) (nd5 w hn)
  unfold SD.GPinst at h1 ⊢
  simp only [act_neg3]
  exact fun ⟨hc1, hc2⟩ =>
    h1 ⟨(gp_eq1 _ _ _ _ _ _ _ _ _).1 hc1, (gp_eq2 _ _ _ _ _ _ _ _ _).1 hc2⟩

/-! ### `Circ` -/

theorem twoAt_xor : ∀ ν x y z c : Bool,
    SD.twoAt (ν ^^ x) (ν ^^ y) (ν ^^ z) c ↔ SD.twoAt x y z (ν ^^ c) := by
  unfold SD.twoAt
  decide

theorem circ_e01 : ∀ ν g0 g1 g2 g3 n x0 x1 : Bool,
    ((ν ^^ g0 ^^ g1 ^^ n) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1)) =
      (ν ^^ (n ^^ x0 ^^ !x1)) := by
  decide

theorem circ_e02 : ∀ ν g0 g1 g2 g3 n x0 x2 : Bool,
    ((ν ^^ g0 ^^ g2 ^^ n) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ (g0 ^^ g1 ^^ g3 ^^ x2)) =
      (ν ^^ (n ^^ x0 ^^ x2)) := by
  decide

theorem circ_e03 : ∀ ν g0 g1 g2 g3 n x0 x3 : Bool,
    ((ν ^^ g0 ^^ g3 ^^ n) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) =
      (ν ^^ (n ^^ x0 ^^ !x3)) := by
  decide

theorem circ_e12 : ∀ ν g0 g1 g2 g3 n x1 x2 : Bool,
    ((ν ^^ g1 ^^ g2 ^^ n) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ (g0 ^^ g1 ^^ g3 ^^ x2)) =
      (ν ^^ (n ^^ !x1 ^^ x2)) := by
  decide

theorem circ_e13 : ∀ ν g0 g1 g2 g3 n x1 x3 : Bool,
    ((ν ^^ g1 ^^ g3 ^^ n) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) =
      (ν ^^ (n ^^ !x1 ^^ !x3)) := by
  decide

theorem circ_e23 : ∀ ν g0 g1 g2 g3 n x2 x3 : Bool,
    ((ν ^^ g2 ^^ g3 ^^ n) ^^ (g0 ^^ g1 ^^ g3 ^^ x2) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) =
      (ν ^^ (n ^^ x2 ^^ !x3)) := by
  decide

/-- Under the symmetry, every edge flag `σ_ij` of the circuit condition is complemented by `ν`
(the reorientation signs cancel), and `twoAt` is symmetric under complementing all flags. -/
theorem circ_core (ν g0 g1 g2 g3 n01 n02 n03 n12 n13 n23 x0 x1 x2 x3 c : Bool)
    (H : SD.twoAt (n01 ^^ x0 ^^ !x1) (n02 ^^ x0 ^^ x2) (n03 ^^ x0 ^^ !x3) (ν ^^ c) ∨
      SD.twoAt (n01 ^^ x0 ^^ !x1) (n12 ^^ !x1 ^^ x2) (n13 ^^ !x1 ^^ !x3) (ν ^^ c) ∨
      SD.twoAt (n02 ^^ x0 ^^ x2) (n12 ^^ !x1 ^^ x2) (n23 ^^ x2 ^^ !x3) (ν ^^ c) ∨
      SD.twoAt (n03 ^^ x0 ^^ !x3) (n13 ^^ !x1 ^^ !x3) (n23 ^^ x2 ^^ !x3) (ν ^^ c)) :
    SD.twoAt ((ν ^^ g0 ^^ g1 ^^ n01) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1))
        ((ν ^^ g0 ^^ g2 ^^ n02) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ (g0 ^^ g1 ^^ g3 ^^ x2))
        ((ν ^^ g0 ^^ g3 ^^ n03) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) c ∨
      SD.twoAt ((ν ^^ g0 ^^ g1 ^^ n01) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1))
        ((ν ^^ g1 ^^ g2 ^^ n12) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ (g0 ^^ g1 ^^ g3 ^^ x2))
        ((ν ^^ g1 ^^ g3 ^^ n13) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) c ∨
      SD.twoAt ((ν ^^ g0 ^^ g2 ^^ n02) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ (g0 ^^ g1 ^^ g3 ^^ x2))
        ((ν ^^ g1 ^^ g2 ^^ n12) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ (g0 ^^ g1 ^^ g3 ^^ x2))
        ((ν ^^ g2 ^^ g3 ^^ n23) ^^ (g0 ^^ g1 ^^ g3 ^^ x2) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) c ∨
      SD.twoAt ((ν ^^ g0 ^^ g3 ^^ n03) ^^ (g1 ^^ g2 ^^ g3 ^^ x0) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3))
        ((ν ^^ g1 ^^ g3 ^^ n13) ^^ !(g0 ^^ g2 ^^ g3 ^^ x1) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3))
        ((ν ^^ g2 ^^ g3 ^^ n23) ^^ (g0 ^^ g1 ^^ g3 ^^ x2) ^^ !(g0 ^^ g1 ^^ g2 ^^ x3)) c := by
  rw [circ_e01, circ_e02, circ_e03, circ_e12, circ_e13, circ_e23]
  simp only [twoAt_xor]
  exact H

theorem circ_act (w : W) {D : SD} (h : D.Circ) : (D.act w).Circ := by
  intro v0 v1 v2 v3 hn
  have h1 := h (w.π v0) (w.π v1) (w.π v2) (w.π v3) (nd4 w hn)
  unfold SD.CircInst at h1 ⊢
  simp only [act_neg3, act_neg2]
  intro c
  exact circ_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h1 (w.ν ^^ c))

/-! ### `Forb` -/

theorem hF_core : ∀ ν gr gs gv n1 n2 x : Bool,
    ((ν ^^ gr ^^ gs ^^ n1) ^^ (ν ^^ gr ^^ gv ^^ n2) ^^ (gr ^^ gs ^^ gv ^^ x)) =
      (gr ^^ (n1 ^^ n2 ^^ x)) := by
  decide

theorem HF_core : ∀ ν gr gs gv n x : Bool,
    (true ^^ (ν ^^ gs ^^ gv ^^ n) ^^ (gr ^^ gs ^^ gv ^^ x)) =
      (ν ^^ gr ^^ (true ^^ n ^^ x)) := by
  decide

theorem aF_core : ∀ gr gs gv gw x1 x2 x3 : Bool,
    ((gr ^^ gs ^^ gv ^^ x1) ^^ (gr ^^ gs ^^ gw ^^ x2) ^^ (gr ^^ gv ^^ gw ^^ x3)) =
      (gr ^^ (x1 ^^ x2 ^^ x3)) := by
  decide

theorem AF_core : ∀ ν gr gs gv gw n x1 x2 x3 : Bool,
    ((ν ^^ gr ^^ gs ^^ n) ^^ (gr ^^ gs ^^ gv ^^ x1) ^^ (gr ^^ gs ^^ gw ^^ x2) ^^
        (gs ^^ gv ^^ gw ^^ x3)) =
      (ν ^^ gr ^^ (n ^^ x1 ^^ x2 ^^ x3)) := by
  decide

theorem wF_core : ∀ ν gr gs gv gw n1 n2 x1 x2 x3 x4 : Bool,
    (true ^^ (ν ^^ gr ^^ gs ^^ n1) ^^ (ν ^^ gv ^^ gw ^^ n2) ^^ (gr ^^ gs ^^ gv ^^ x1) ^^
        (gr ^^ gs ^^ gw ^^ x2) ^^ (gr ^^ gv ^^ gw ^^ x3) ^^ (gs ^^ gv ^^ gw ^^ x4)) =
      (true ^^ n1 ^^ n2 ^^ x1 ^^ x2 ^^ x3 ^^ x4) := by
  decide

theorem hF_act (w : W) (D : SD) (r s v : Fin 8) :
    (D.act w).hF r s v = (w.g r ^^ D.hF (w.π r) (w.π s) (w.π v)) := by
  unfold SD.hF
  simp only [act_neg3, act_neg2]
  exact hF_core _ _ _ _ _ _ _

theorem HF_act (w : W) (D : SD) (r s v : Fin 8) :
    (D.act w).HF r s v = (w.ν ^^ w.g r ^^ D.HF (w.π r) (w.π s) (w.π v)) := by
  unfold SD.HF
  simp only [act_neg3, act_neg2]
  exact HF_core _ _ _ _ _ _

theorem aF_act (w : W) (D : SD) (r s v u : Fin 8) :
    (D.act w).aF r s v u = (w.g r ^^ D.aF (w.π r) (w.π s) (w.π v) (w.π u)) := by
  unfold SD.aF
  simp only [act_neg3]
  exact aF_core _ _ _ _ _ _ _

theorem AF_act (w : W) (D : SD) (r s v u : Fin 8) :
    (D.act w).AF r s v u = (w.ν ^^ w.g r ^^ D.AF (w.π r) (w.π s) (w.π v) (w.π u)) := by
  unfold SD.AF
  simp only [act_neg3, act_neg2]
  exact AF_core _ _ _ _ _ _ _ _ _

theorem wF_act (w : W) (D : SD) (r s v u : Fin 8) :
    (D.act w).wF r s v u = D.wF (w.π r) (w.π s) (w.π v) (w.π u) := by
  unfold SD.wF
  simp only [act_neg3, act_neg2]
  exact wF_core _ _ _ _ _ _ _ _ _ _ _

/-- Cancelling a common flag from a sum of two terms. -/
theorem xor_pair : ∀ a x y : Bool, ((a ^^ x) ^^ (a ^^ y)) = (x ^^ y) := by
  decide

/-- The pattern equations of `ForbInst` are invariant: `h*` and `a*` both gain `g r`, `H*` and `A*`
both gain `ν ^^ g r`, and `w*` is unchanged. -/
theorem forb_act (w : W) {D : SD} (h : D.Forb) : (D.act w).Forb := by
  intro r s i j k hn
  have h1 := h (w.π r) (w.π s) (w.π i) (w.π j) (w.π k) (nd5 w hn)
  unfold SD.ForbInst at h1 ⊢
  simp only [hF_act, HF_act, aF_act, AF_act, wF_act, Bool.xor_right_inj, xor_pair]
  exact h1

end KAct

theorem SD.Valid8.act (w : W) {D : SD} (h : D.Valid8) : (D.act w).Valid8 :=
  ⟨KAct.wf_act w h.1, KAct.gp_act w h.2.1, KAct.circ_act w h.2.2.1, KAct.forb_act w h.2.2.2⟩

end Results.EightEquidistantLines
