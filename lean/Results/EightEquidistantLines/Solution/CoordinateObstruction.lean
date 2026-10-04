import Results.EightEquidistantLines.Solution.Family
import Mathlib.Data.Finset.Card

namespace Results.EightEquidistantLines.CoordinateObstruction

open V3

private theorem skew_sq (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (h : cross (F.u i) (F.u j) ≠ 0) :
    det (F.p i - F.p j) (F.u i) (F.u j) ^ 2 = norm2 (cross (F.u i) (F.u j)) := by
  have hd := F.dist1 i j hij
  rw [lineDist3_skew _ _ _ _ h] at hd
  have hn : 0 < norm2 (cross (F.u i) (F.u j)) :=
    lt_of_le_of_ne (norm2_nonneg _) (fun hz => h ((norm2_eq_zero_iff _).mp hz.symm))
  have he := (div_eq_iff (Real.sqrt_pos.mpr hn).ne').mp hd
  have hs := Real.sq_sqrt hn.le
  have ha := sq_abs (det (F.p i - F.p j) (F.u i) (F.u j))
  rw [← ha, he]
  simpa only [one_mul] using hs

private theorem par_sq (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (h : cross (F.u i) (F.u j) = 0) :
    norm2 (F.p i - F.p j) - dot (F.p i - F.p j) (F.u i) ^ 2 = 1 := by
  have hj : F.u j ≠ 0 := by
    intro hz
    have hu := F.unit j
    simp [hz, norm2, dot] at hu
  have hd := F.dist1 i j hij
  rw [lineDist3_parallel _ _ _ _ (F.unit i) hj h] at hd
  have hn := norm2_nonneg (cross (F.p i - F.p j) (F.u i))
  rw [norm2_cross, F.unit i, mul_one] at hn
  have hs := Real.sq_sqrt hn
  rw [hd] at hs
  norm_num at hs
  exact hs.symm

private theorem axis_iff (u : V3) :
    cross (⟨1, 0, 0⟩ : V3) u = 0 ↔ u.y = 0 ∧ u.z = 0 := by
  constructor
  · intro h
    have hy := congrArg V3.y h
    have hz := congrArg V3.z h
    simp only [cross_y, cross_z, zero_y, zero_z] at hy hz
    constructor <;> linarith
  · rintro ⟨hy, hz⟩
    ext <;> simp [hy, hz]

private theorem axis_sq (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (hiy : (F.u i).y = 0) (hiz : (F.u i).z = 0)
    (hjy : (F.u j).y = 0) (hjz : (F.u j).z = 0) :
    ((F.p i).y - (F.p j).y)^2 + ((F.p i).z - (F.p j).z)^2 = 1 := by
  have hp : cross (F.u i) (F.u j) = 0 := by
    ext <;> simp [hiy, hiz, hjy, hjz]
  have h := par_sq F i j hij hp
  have hu := F.unit i
  simp only [norm2, dot, hiy, hiz, mul_zero, add_zero] at hu
  have hm := congrArg (fun t : ℝ => ((F.p i).x - (F.p j).x)^2 * t) hu
  simp only [norm2, dot, sub_x, sub_y, sub_z, hiy, hiz, mul_zero, add_zero] at h
  nlinarith only [h, hm]

private theorem axis_sign (F : UFam) (i : Fin 8)
    (hy : (F.u i).y = 0) (hz : (F.u i).z = 0) :
    (F.u i).x = 1 ∨ (F.u i).x = -1 := by
  have h := F.unit i
  simp only [norm2, dot, hy, hz, mul_zero, add_zero] at h
  exact mul_self_eq_one_iff.mp h

/-- The two displayed equations in the manuscript force a non-axis line into `z = ±1`. -/
private theorem nonaxis_coords (F : UFam) (a b i : Fin 8)
    (hpa : F.p a = 0) (hua : F.u a = ⟨1, 0, 0⟩)
    (hby : (F.p b).y = 1) (hbz : (F.p b).z = 0)
    (huby : (F.u b).y = 0) (hubz : (F.u b).z = 0)
    (hi : ¬ ((F.u i).y = 0 ∧ (F.u i).z = 0)) :
    (F.u i).z = 0 ∧ (F.u i).y ≠ 0 ∧ (F.p i).z ^ 2 = 1 := by
  have hai : a ≠ i := by
    intro he
    subst i
    exact hi (by simp [hua])
  have hbi : b ≠ i := by
    intro he
    subst i
    exact hi ⟨huby, hubz⟩
  have hcai : cross (F.u a) (F.u i) ≠ 0 := by
    intro hz
    rw [hua] at hz
    exact hi ((axis_iff _).mp hz)
  have hbiSign := axis_sign F b huby hubz
  have hcbi : cross (F.u b) (F.u i) ≠ 0 := by
    intro hc
    have hcy := congrArg V3.y hc
    have hcz := congrArg V3.z hc
    rcases hbiSign with hx | hx <;>
      simp [cross_y, cross_z, huby, hubz, hx] at hcy hcz <;>
      exact hi ⟨hcz, hcy⟩
  have ha := skew_sq F a i hai hcai
  have hb := skew_sq F b i hbi hcbi
  let A : ℝ := -(F.p i).y * (F.u i).z + (F.p i).z * (F.u i).y
  have hea : A^2 = (F.u i).y^2 + (F.u i).z^2 := by
    simp only [hpa, hua, det_eq, norm2, dot, cross_x, cross_y, cross_z,
      sub_x, sub_y, sub_z, zero_x, zero_y, zero_z] at ha
    convert ha using 1 <;> (try dsimp only [A]) <;> ring
  have heb : (A + (F.u i).z)^2 = (F.u i).y^2 + (F.u i).z^2 := by
    rcases hbiSign with hx | hx <;>
      simp only [det_eq, norm2, dot, cross_x, cross_y, cross_z,
        sub_x, sub_y, sub_z, hby, hbz, huby, hubz, hx] at hb <;>
      convert hb using 1 <;> (try dsimp only [A]) <;> ring
  have hprod : (F.u i).z * (2*A + (F.u i).z) = 0 := by nlinarith only [hea, heb]
  have hiz : (F.u i).z = 0 := by
    rcases mul_eq_zero.mp hprod with hz | hh
    · exact hz
    · have hA : A = -(F.u i).z / 2 := by linarith
      rw [hA] at hea
      nlinarith only [hea, sq_nonneg (F.u i).y, sq_nonneg (F.u i).z]
  have hiy : (F.u i).y ≠ 0 := by
    intro hy
    exact hi ⟨hy, hiz⟩
  refine ⟨hiz, hiy, ?_⟩
  have heprod : ((F.p i).z^2 - 1) * (F.u i).y^2 = 0 := by
    dsimp [A] at hea
    rw [hiz] at hea
    nlinarith only [hea]
  exact sub_eq_zero.mp ((mul_eq_zero.mp heprod).resolve_right (pow_ne_zero _ hiy))

private theorem parallel_sign (F : UFam) (c i : Fin 8)
    (h : cross (F.u c) (F.u i) = 0) :
    F.u i = F.u c ∨ F.u i = -F.u c := by
  have hn := norm2_cross (F.u c) (F.u i)
  rw [h, F.unit c, F.unit i] at hn
  rw [show norm2 (0 : V3) = 0 by norm_num [norm2, dot]] at hn
  have hs : dot (F.u c) (F.u i) * dot (F.u c) (F.u i) = 1 := by nlinarith only [hn]
  have he := LineDist.par_eq (F.u c) (F.u i) (F.unit c) h
  rcases mul_self_eq_one_iff.mp hs with hp | hm
  · left
    rw [hp] at he
    simpa only [show (1 : ℝ) • F.u c = F.u c by ext <;> simp] using he
  · right
    rw [hm] at he
    simpa only [show (-1 : ℝ) • F.u c = -F.u c by ext <;> simp] using he

/-- In one horizontal plane, parallel lines have the ordinary one-dimensional
projected-coordinate distance. -/
private theorem projected_sq (F : UFam) (c i j : Fin 8) (hij : i ≠ j)
    (hcz : (F.u c).z = 0) (hzi : (F.p i).z = (F.p j).z)
    (hci : cross (F.u c) (F.u i) = 0) (hijpar : cross (F.u i) (F.u j) = 0) :
    (((F.p i).x * (F.u c).y - (F.p i).y * (F.u c).x) -
      ((F.p j).x * (F.u c).y - (F.p j).y * (F.u c).x))^2 = 1 := by
  have hp := par_sq F i j hij hijpar
  have hu := F.unit c
  simp only [norm2, dot, hcz, mul_zero, add_zero] at hu
  have hm := congrArg (fun t : ℝ =>
    (((F.p i).x - (F.p j).x)^2 + ((F.p i).y - (F.p j).y)^2) * t) hu
  rcases parallel_sign F c i hci with hplus | hminus
  · rw [hplus] at hp
    simp only [norm2, dot, sub_x, sub_y, sub_z, hzi, sub_self, hcz,
      mul_zero, add_zero] at hp
    nlinarith only [hp, hm]
  · rw [hminus] at hp
    simp only [norm2, dot, sub_x, sub_y, sub_z, neg_x, neg_y, neg_z,
      hzi, sub_self, hcz, neg_zero, mul_zero, add_zero] at hp
    nlinarith only [hp, hm]

private theorem three_reals (x y z : ℝ)
    (hxy : (x-y)^2 = 1) (hxz : (x-z)^2 = 1) (hyz : (y-z)^2 = 1) : False := by
  have h₁ : (x-y)*(x-y) = 1 := by nlinarith
  have h₂ : (y-z)*(y-z) = 1 := by nlinarith
  rcases mul_self_eq_one_iff.mp h₁ with h₁ | h₁ <;>
    rcases mul_self_eq_one_iff.mp h₂ with h₂ | h₂ <;> nlinarith only [h₁, h₂, hxz]

private theorem horizontal_skew_z (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (hiz : (F.u i).z = 0) (hjz : (F.u j).z = 0)
    (hc : cross (F.u i) (F.u j) ≠ 0) :
    ((F.p i).z - (F.p j).z)^2 = 1 := by
  let C : ℝ := (F.u i).x * (F.u j).y - (F.u i).y * (F.u j).x
  have hC : C ≠ 0 := by
    intro he
    apply hc
    ext <;> simp [cross_x, cross_y, cross_z, hiz, hjz, C] at he ⊢
    exact he
  have h := skew_sq F i j hij hc
  simp only [det_eq, norm2, dot, cross_x, cross_y, cross_z, sub_x, sub_y,
    sub_z, hiz, hjz, mul_zero, zero_mul, sub_self,
    add_zero, zero_add] at h
  have hp : (((F.p i).z - (F.p j).z)^2 - 1) * C^2 = 0 := by
    dsimp [C]
    nlinarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (pow_ne_zero _ hC))

private theorem horizontal_par_bound (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (hiz : (F.u i).z = 0) (hc : cross (F.u i) (F.u j) = 0) :
    ((F.p i).z - (F.p j).z)^2 ≤ 1 := by
  have hp := par_sq F i j hij hc
  have hu := F.unit i
  simp only [norm2, dot, hiz, mul_zero, add_zero] at hu
  have hm := congrArg (fun t : ℝ =>
    (((F.p i).x - (F.p j).x)^2 + ((F.p i).y - (F.p j).y)^2) * t) hu
  simp only [norm2, dot, sub_x, sub_y, sub_z, hiz, mul_zero, add_zero] at hp
  nlinarith only [hp, hm, sq_nonneg
    (((F.p i).x - (F.p j).x) * (F.u i).y -
      ((F.p i).y - (F.p j).y) * (F.u i).x)]

private theorem signs_of_sq_one (x : ℝ) (h : x^2 = 1) : x = 1 ∨ x = -1 :=
  mul_self_eq_one_iff.mp (by nlinarith only [h])

/-- Non-axis lines are in the same horizontal plane and are mutually parallel. -/
private theorem plane_pair (F : UFam) (i j : Fin 8) (hij : i ≠ j)
    (hiz : (F.u i).z = 0) (hjz : (F.u j).z = 0)
    (hip : (F.p i).z^2 = 1) (hjp : (F.p j).z^2 = 1) :
    cross (F.u i) (F.u j) = 0 ∧ (F.p i).z = (F.p j).z := by
  have hc : cross (F.u i) (F.u j) = 0 := by
    by_contra hne
    have h := horizontal_skew_z F i j hij hiz hjz hne
    rcases signs_of_sq_one _ hip with hi | hi <;>
      rcases signs_of_sq_one _ hjp with hj | hj <;>
      rw [hi, hj] at h <;> norm_num at h
  refine ⟨hc, ?_⟩
  have h := horizontal_par_bound F i j hij hiz hc
  rcases signs_of_sq_one _ hip with hi | hi <;>
    rcases signs_of_sq_one _ hjp with hj | hj <;>
    first | exact hi.trans hj.symm | norm_num [hi, hj] at h

private theorem third_axis_coords (F : UFam) (a b i : Fin 8)
    (hai : a ≠ i) (hbi : b ≠ i)
    (hpa : F.p a = 0) (hua : F.u a = ⟨1, 0, 0⟩)
    (hby : (F.p b).y = 1) (hbz : (F.p b).z = 0)
    (huby : (F.u b).y = 0) (hubz : (F.u b).z = 0)
    (huiy : (F.u i).y = 0) (huiz : (F.u i).z = 0) :
    (F.p i).y = 1/2 ∧ (F.p i).z^2 = 3/4 := by
  have ha := axis_sq F a i hai (by simp [hua]) (by simp [hua]) huiy huiz
  have hb := axis_sq F b i hbi huby hubz huiy huiz
  simp only [hpa, zero_y, zero_z] at ha
  rw [hby, hbz] at hb
  have hy : (F.p i).y = 1/2 := by nlinarith only [ha, hb]
  refine ⟨hy, ?_⟩
  rw [hy] at ha
  nlinarith only [ha]

/-- A third original-direction line cannot coexist with a non-axis line. -/
private theorem third_axis_excluded (F : UFam) (q c : Fin 8)
    (hqy : (F.u q).y = 0) (hqz : (F.u q).z = 0)
    (hqp : (F.p q).z^2 = 3/4)
    (hcy : (F.u c).y ≠ 0) (hcz : (F.u c).z = 0)
    (hcp : (F.p c).z^2 = 1) : False := by
  have hqc : q ≠ c := by
    intro he
    subst q
    exact hcy hqy
  have hc : cross (F.u q) (F.u c) ≠ 0 := by
    intro he
    have hz := congrArg V3.z he
    rcases axis_sign F q hqy hqz with hx | hx <;>
      simp [cross_z, hqy, hx] at hz <;> exact hcy hz
  have h := horizontal_skew_z F q c hqc hqz hcz hc
  rcases signs_of_sq_one _ hcp with hc | hc <;>
    rw [hc] at h <;> nlinarith only [h, hqp]

private theorem outside_four (a b c d : Fin 8) :
    ∃ e : Fin 8, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by
  classical
  let s : Finset (Fin 8) := {a, b, c, d}
  have hs : s.card < 8 := by
    have h₁ := Finset.card_insert_le a ({b,c,d} : Finset (Fin 8))
    have h₂ := Finset.card_insert_le b ({c,d} : Finset (Fin 8))
    have h₃ := Finset.card_insert_le c ({d} : Finset (Fin 8))
    have h₄ := Finset.card_singleton d
    dsimp [s]
    omega
  have he : ∃ e : Fin 8, e ∉ s := by
    by_contra h
    have hall : ∀ e, e ∈ s := fun e => Classical.byContradiction (fun he => h ⟨e, he⟩)
    have hh : s = Finset.univ := Finset.eq_univ_of_forall hall
    rw [hh] at hs
    norm_num at hs
  obtain ⟨e, he⟩ := he
  refine ⟨e, ?_⟩
  simpa only [s, Finset.mem_insert, Finset.mem_singleton, not_or] using he

/-- The manuscript's coordinate case proves that a normalized eight-line
unit-distance family containing the displayed parallel bases cannot exist. -/
theorem normalized_false (F : UFam) (a b : Fin 8) (_hab : a ≠ b)
    (hpa : F.p a = 0) (hua : F.u a = ⟨1, 0, 0⟩)
    (hby : (F.p b).y = 1) (hbz : (F.p b).z = 0)
    (hpar : cross (F.u a) (F.u b) = 0) : False := by
  classical
  have hbaxis : (F.u b).y = 0 ∧ (F.u b).z = 0 := by
    rw [hua] at hpar
    exact (axis_iff _).mp hpar
  have coords := nonaxis_coords F a b
    (hpa := hpa) (hua := hua) (hby := hby) (hbz := hbz)
    (huby := hbaxis.1) (hubz := hbaxis.2)
  have third := third_axis_coords F a b
    (hpa := hpa) (hua := hua) (hby := hby) (hbz := hbz)
    (huby := hbaxis.1) (hubz := hbaxis.2)
  by_cases hex : ∃ c : Fin 8, ¬ ((F.u c).y = 0 ∧ (F.u c).z = 0)
  · obtain ⟨c, hc⟩ := hex
    obtain ⟨hcz, hcy, hcp⟩ := coords c hc
    have only_bases : ∀ i, (F.u i).y = 0 ∧ (F.u i).z = 0 → i = a ∨ i = b := by
      intro i hi
      by_cases hia : i = a
      · exact Or.inl hia
      by_cases hib : i = b
      · exact Or.inr hib
      have hip := (third i (Ne.symm hia) (Ne.symm hib) hi.1 hi.2).2
      exact (third_axis_excluded F i c hi.1 hi.2 hip hcy hcz hcp).elim
    obtain ⟨d, hda, hdb, hdc, _⟩ := outside_four a b c c
    obtain ⟨e, hea, heb, hec, hed⟩ := outside_four a b c d
    have hd : ¬ ((F.u d).y = 0 ∧ (F.u d).z = 0) := by
      intro hi
      exact (only_bases d hi).elim hda hdb
    have he : ¬ ((F.u e).y = 0 ∧ (F.u e).z = 0) := by
      intro hi
      exact (only_bases e hi).elim hea heb
    obtain ⟨hdz, _, hdp⟩ := coords d hd
    obtain ⟨hez, _, hep⟩ := coords e he
    have hcd := plane_pair F c d (Ne.symm hdc) hcz hdz hcp hdp
    have hce := plane_pair F c e (Ne.symm hec) hcz hez hcp hep
    have hde := plane_pair F d e (Ne.symm hed) hdz hez hdp hep
    exact three_reals
      ((F.p c).x * (F.u c).y - (F.p c).y * (F.u c).x)
      ((F.p d).x * (F.u c).y - (F.p d).y * (F.u c).x)
      ((F.p e).x * (F.u c).y - (F.p e).y * (F.u c).x)
      (projected_sq F c c d (Ne.symm hdc) hcz hcd.2 (cross_self _) hcd.1)
      (projected_sq F c c e (Ne.symm hec) hcz hce.2 (cross_self _) hce.1)
      (projected_sq F c d e (Ne.symm hed) hcz hde.2 hcd.1 hde.1)
  · have hall : ∀ i, (F.u i).y = 0 ∧ (F.u i).z = 0 := by
      intro i
      exact Classical.byContradiction (fun hi => hex ⟨i, hi⟩)
    obtain ⟨c, hca, hcb, _, _⟩ := outside_four a b a b
    obtain ⟨d, hda, hdb, hdc, _⟩ := outside_four a b c c
    have hc := third c (Ne.symm hca) (Ne.symm hcb) (hall c).1 (hall c).2
    have hd := third d (Ne.symm hda) (Ne.symm hdb) (hall d).1 (hall d).2
    have h := axis_sq F c d (Ne.symm hdc) (hall c).1 (hall c).2 (hall d).1 (hall d).2
    rw [hc.1, hd.1] at h
    have hp : ((F.p c).z - (F.p d).z) * ((F.p c).z + (F.p d).z) = 0 := by
      nlinarith only [hc.2, hd.2]
    rcases mul_eq_zero.mp hp with hp | hp <;> nlinarith only [h, hp, hc.2, hd.2]

end Results.EightEquidistantLines.CoordinateObstruction
