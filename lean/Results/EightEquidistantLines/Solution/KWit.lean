import Results.EightEquidistantLines.Solution.KAct
import Results.EightEquidistantLines.Solution.KEqn

/-!
# Soundness of the symmetry-witness check

If `witOk m x r pi g nu` holds and `x` represents `D` on the labels `< m`, then some symmetry `w`
makes `D.act w` represented by `r` on the labels `< m`.  `zipCheck_sound` extracts the witness for
a leaf of a checked list.

Proof outline.  `allBelow_iff` turns the boolean check into its quantified form.  The packed
permutation defines a self-map `piMap` of `Fin 8` (the identity above `m`), injective by the
first part of the check.  The sorting lemma `xBit_eq` (for partial agreement `AgreeJ m`) identifies
`xBit x (π a) (π b) (π c)` with `D.neg3 (π a) (π b) (π c)` for distinct labels `< m`, and `eBit_eq`
does the same for the distance signs; the other two parts of the check then say exactly that
`r` agrees with `D.act w` on the labels `< m`.
-/

namespace Results.EightEquidistantLines

open Kc

namespace KWit

/-! ### Boolean helpers -/

theorem not_xor_eq_true {p q : Bool} (h : (!(p ^^ q)) = true) : p = q := by
  revert h; revert p q; decide

theorem xor4 (a b c d : Bool) : ((a ^^ b) ^^ (c ^^ d)) = (a ^^ b ^^ c ^^ d) := by
  revert a b c d; decide

/-- `allBelow n P = true` iff `P k = true` for every `k < n`. -/
theorem allBelow_iff (n : Nat) (P : Nat → Bool) :
    Kc.allBelow n P = true ↔ ∀ k, k < n → P k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    have e : Kc.allBelow (n + 1) P = (Kc.allBelow n P && P n) := rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

/-! ### The sorting lemma for partial agreement -/

theorem nodup3 {a b c : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : [a, b, c].Nodup := by
  simp [hab, hac, hbc]

/-- The five values of `neg3` on the other permutations of a distinct triple. -/
theorem perm3 {D : SD} (hD : D.Wf) {a b c : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    D.neg3 b a c = !D.neg3 a b c ∧ D.neg3 a c b = !D.neg3 a b c ∧
    D.neg3 c a b = D.neg3 a b c ∧ D.neg3 b c a = D.neg3 a b c ∧ D.neg3 c b a = !D.neg3 a b c := by
  obtain ⟨h1, h2, -⟩ := hD
  have e1 := h1 a b c (nodup3 hab hac hbc)
  have e2 := h2 a b c (nodup3 hab hac hbc)
  have e3 := h1 c a b (nodup3 hac.symm hbc.symm hab)
  have e4 := h2 b a c (nodup3 hab.symm hbc hac)
  have e5 := h1 b c a (nodup3 hbc hab.symm hac.symm)
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · -- neg3 c a b: e3 : neg3 a c b = !neg3 c a b, e2 : neg3 a c b = !neg3 a b c
    rw [e2] at e3
    revert e3; generalize D.neg3 a b c = u; generalize D.neg3 c a b = v; revert u v; decide
  · -- neg3 b c a: e4 : neg3 b c a = !neg3 b a c, e1 : neg3 b a c = !neg3 a b c
    rw [e1] at e4
    rw [e4]; simp
  · -- neg3 c b a: e5 : neg3 c b a = !neg3 b c a
    rw [e5, e4, e1]; simp

/-- The sorting lemma for the joint bit-vector, valid under partial agreement: for distinct labels
`< m`, `xBit x a b c` is the sign `D.neg3 a b c` of the (unsorted) triple. -/
theorem xBit_eq {m : Nat} {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ m D x) {a b c : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < m) (hb : b.val < m)
    (hc : c.val < m) : xBit x a.val b.val c.val = D.neg3 a b c := by
  obtain ⟨hx3, -⟩ := hx
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  obtain ⟨p1, p2, p3, p4, p5⟩ := perm3 hD hab hac hbc
  unfold xBit xT
  split_ifs with h1 h2 h3 h4 h5
  · rw [hx3 a b c (Fin.lt_def.2 h1) (Fin.lt_def.2 h2) hc]; simp
  · rw [hx3 a c b (Fin.lt_def.2 h3) (Fin.lt_def.2 (by omega)) hb, p2]; simp
  · rw [hx3 c a b (Fin.lt_def.2 (by omega)) (Fin.lt_def.2 h1) hb, p3]; simp
  · rw [hx3 b a c (Fin.lt_def.2 (by omega)) (Fin.lt_def.2 h4) hc, p1]; simp
  · rw [hx3 b c a (Fin.lt_def.2 h5) (Fin.lt_def.2 (by omega)) ha, p4]; simp
  · rw [hx3 c b a (Fin.lt_def.2 (by omega)) (Fin.lt_def.2 (by omega)) ha, p5]; simp

/-- The same for the distance signs: for distinct labels `< m`, `eBit x a b` is `D.neg2 a b`. -/
theorem eBit_eq {m : Nat} {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ m D x) {a b : Fin 8}
    (hab : a ≠ b) (ha : a.val < m) (hb : b.val < m) : eBit x a.val b.val = D.neg2 a b := by
  obtain ⟨-, hx2⟩ := hx
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  unfold eBit
  split_ifs with h1
  · exact hx2 a b (Fin.lt_def.2 h1) hb
  · rw [hx2 b a (Fin.lt_def.2 (by omega)) ha]
    exact hD.2.2 a b

/-! ### The permutation defined by the packed digits -/

/-- The self-map of `Fin 8` determined by the first `m` three-bit digits of `pi`
(the identity on the labels `≥ m`). -/
def piMap (m pi : Nat) (h8 : ∀ a, a < m → piGet pi a < 8) (a : Fin 8) : Fin 8 :=
  if h : a.val < m then ⟨piGet pi a.val, h8 _ h⟩ else a

theorem piMap_val {m pi : Nat} {h8 : ∀ a, a < m → piGet pi a < 8} {a : Fin 8} (ha : a.val < m) :
    (piMap m pi h8 a).val = piGet pi a.val := by
  simp [piMap, ha]

theorem piMap_inj {m pi : Nat} (h8 : ∀ a, a < m → piGet pi a < 8)
    (hlt : ∀ a, a < m → piGet pi a < m)
    (hne : ∀ a b, a < m → b < m → piGet pi a = piGet pi b → a = b) :
    Function.Injective (piMap m pi h8) := by
  intro a b hab
  by_cases ha : a.val < m <;> by_cases hb : b.val < m
  · have e := congrArg Fin.val hab
    rw [piMap_val ha, piMap_val hb] at e
    exact Fin.ext (hne _ _ ha hb e)
  · have e := congrArg Fin.val hab
    rw [piMap_val ha] at e
    simp only [piMap, hb, dif_neg, not_false_eq_true] at e
    have := hlt _ ha
    omega
  · have e := congrArg Fin.val hab
    rw [piMap_val hb] at e
    simp only [piMap, ha, dif_neg, not_false_eq_true] at e
    have := hlt _ hb
    omega
  · simp only [piMap, ha, hb, dif_neg, not_false_eq_true] at hab
    exact hab

end KWit

theorem Kc.witOk_sound (m : Nat) (hm : m ≤ 8) (D : SD) (hD : D.Wf) (x r pi g : Nat) (nu : Bool)
    (hx : AgreeJ m D x) (h : Kc.witOk m x r pi g nu = true) : ∃ w : W, AgreeJ m (D.act w) r := by
  unfold Kc.witOk at h
  simp only [Bool.and_eq_true, KWit.allBelow_iff] at h
  obtain ⟨hA, hB, hC⟩ := h
  -- (a) the digits of `pi` are an injective map of `{0..m-1}` into itself
  have hlt : ∀ a, a < m → piGet pi a < m := by
    intro a ha
    have h1 := Nat.le_of_ble_eq_true (hA a ha).1
    omega
  have hne : ∀ a b, a < m → b < m → piGet pi a = piGet pi b → a = b := by
    intro a b ha hb hab
    have h1 := (hA a ha).2 b hb
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Nat.eq_of_beq_eq_true h1
    · simp [hab] at h1
  have h8 : ∀ a, a < m → piGet pi a < 8 := fun a ha => lt_of_lt_of_le (hlt a ha) hm
  have hinj := KWit.piMap_inj h8 hlt hne
  have hrv : ∀ a : Fin 8, a.val < m → (KWit.piMap m pi h8 a).val = piGet pi a.val :=
    fun a ha => KWit.piMap_val ha
  have hrl : ∀ a : Fin 8, a.val < m → (KWit.piMap m pi h8 a).val < m := by
    intro a ha
    rw [hrv a ha]
    exact hlt _ ha
  refine ⟨⟨KWit.piMap m pi h8, hinj, fun a => g.testBit a.val, nu⟩, ?_, ?_⟩
  · -- (b) the triple signs
    intro a b c hab hbc hc
    have hab' : a.val < b.val := Fin.lt_def.1 hab
    have hbc' : b.val < c.val := Fin.lt_def.1 hbc
    have hb : b.val < m := lt_trans hbc' hc
    have ha : a.val < m := lt_trans hab' hb
    have e := KWit.not_xor_eq_true (hB c.val hc b.val hbc' a.val hab')
    have hx3 := KWit.xBit_eq hD hx (a := KWit.piMap m pi h8 a) (b := KWit.piMap m pi h8 b)
      (c := KWit.piMap m pi h8 c) (fun h => absurd (hinj h) (Fin.ne_of_lt hab))
      (fun h => absurd (hinj h) (Fin.ne_of_lt (Fin.lt_trans hab hbc)))
      (fun h => absurd (hinj h) (Fin.ne_of_lt hbc)) (hrl a ha) (hrl b hb) (hrl c hc)
    rw [hrv a ha, hrv b hb, hrv c hc] at hx3
    show r.testBit (triIdx a b c) = (g.testBit a.val ^^ g.testBit b.val ^^ g.testBit c.val ^^
      D.neg3 (KWit.piMap m pi h8 a) (KWit.piMap m pi h8 b) (KWit.piMap m pi h8 c))
    rw [e, hx3, KWit.xor4]
  · -- (c) the pair signs
    intro a b hab hb
    have hab' : a.val < b.val := Fin.lt_def.1 hab
    have ha : a.val < m := lt_trans hab' hb
    have e := KWit.not_xor_eq_true (hC b.val hb a.val hab')
    have hx2 := KWit.eBit_eq hD hx (a := KWit.piMap m pi h8 a) (b := KWit.piMap m pi h8 b)
      (fun h => absurd (hinj h) (Fin.ne_of_lt hab)) (hrl a ha) (hrl b hb)
    rw [hrv a ha, hrv b hb] at hx2
    show r.testBit (vE a b) = (nu ^^ g.testBit a.val ^^ g.testBit b.val ^^
      D.neg2 (KWit.piMap m pi h8 a) (KWit.piMap m pi h8 b))
    rw [e, hx2, KWit.xor4]

theorem Kc.zipCheck_sound (m : Nat) (hm : m ≤ 8) (reps : List Nat) (ls : List Nat)
    (ws : List (Nat × Nat × Nat × Nat)) (h : Kc.zipCheck m reps ls ws = true) (D : SD) (hD : D.Wf)
    (l : Nat) (hl : l ∈ ls) (hx : AgreeJ m D l) :
    ∃ w : W, ∃ ri, ri < reps.length ∧ AgreeJ m (D.act w) (reps.getD ri 0) := by
  induction ls generalizing ws with
  | nil => exact absurd hl (List.not_mem_nil)
  | cons l' ls ih =>
    cases ws with
    | nil =>
      rw [Kc.zipCheck.eq_3 m reps (l' :: ls) [] (by simp) (by simp)] at h
      exact absurd h Bool.false_ne_true
    | cons wt ws =>
      obtain ⟨ri, pi, g, nu⟩ := wt
      rw [Kc.zipCheck.eq_2] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rcases List.mem_cons.1 hl with hl' | hl'
      · subst hl'
        obtain ⟨w, hw⟩ := Kc.witOk_sound m hm D hD l (reps.getD ri 0) pi g (Nat.beq nu 1) hx h2
        exact ⟨w, ri, Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h1), hw⟩
      · exact ih ws h3 hl'

end Results.EightEquidistantLines
