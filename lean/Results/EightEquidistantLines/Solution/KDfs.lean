import Results.EightEquidistantLines.Solution.KEqn
import Results.EightEquidistantLines.Solution.KPack

/-!
# Completeness of the bit-parallel depth-first search

`Kc.Lv.Valid n insts lv` says the packed level data `lv` is the one computed from the instance list
`insts` for the extension by label `n`.  `Kc.leaves_complete` : for every valid sign datum `D` whose
restriction to the labels `< n` is represented by `y` (with no bits on the new variables), the search
returns a joint bit-vector `x` representing `D` on the labels `≤ n`.

Proof outline (namespace `KDfs`).  Fix a joint bit-vector `xs` representing `D` on all eight labels.
The *true path* of the search at depth `d` is the bit-vector `x` with
`x.testBit w = y.testBit w || (w ∈ (orderOf n).take d && xs.testBit w)` (`PathX`).
* `Plane`: the packed state `q` records, at bit `e * S + s`, whether equation `e` of system `s` is
  satisfied by `x` (`st`, a parity of the code against `x`).  It holds initially
  (`Setup.plane_init`) and is preserved by the XOR with a column when a new variable is set
  (`Setup.plane_flip`).
* `Setup.no_prune`: a node on the true path is never pruned: a completely assigned system with all
  eight equations satisfied would give an instance all of whose equations are satisfied by `xs`
  (`Setup.path_agree`: the toggled variables agree on `x` and `xs`), contradicting `Inst.sound` and
  `Inst.holds_of_valid`.
* `Setup.dfs`: induction over the remaining search steps; the leaf of the true path is returned.
-/

namespace Results.EightEquidistantLines

open Kc

/-- The packed level data is the one computed from the instances. -/
def Kc.Lv.Valid (n : Nat) (insts : List Kc.Inst) (lv : Kc.Lv) : Prop :=
  lv.rows = insts.map Kc.Inst.row ∧
  lv.cols = (List.range 84).map (Kc.colSpec lv.rows) ∧
  lv.kp = Kc.kpSpec lv.rows ∧
  lv.done = Kc.doneSpec n lv.rows ∧
  lv.rows.length ≤ 598 ∧
  ∀ i ∈ insts, i.wfB n = true

namespace KDfs

/-! ### Exclusive-or folds and parities -/

theorem xfold_xor (L : List Nat) (g : Nat → Bool) (a b : Bool) :
    L.foldl (fun acc w => acc ^^ g w) (a ^^ b) = (a ^^ L.foldl (fun acc w => acc ^^ g w) b) := by
  induction L generalizing b with
  | nil => rfl
  | cons w L ih =>
    simp only [List.foldl_cons]
    rw [Bool.xor_assoc, ih]

theorem xfold_congr (L : List Nat) (g h : Nat → Bool) (hgh : ∀ w ∈ L, g w = h w) (a : Bool) :
    L.foldl (fun acc w => acc ^^ g w) a = L.foldl (fun acc w => acc ^^ h w) a := by
  induction L generalizing a with
  | nil => rfl
  | cons w L ih =>
    simp only [List.foldl_cons]
    rw [hgh w List.mem_cons_self]
    exact ih (fun u hu => hgh u (List.mem_cons_of_mem _ hu)) _

/-- Changing the summand at a single position `v` (occurring once in `L`). -/
theorem xfold_flip (L : List Nat) (hL : L.Nodup) (v : Nat) (hv : v ∈ L) (g h : Nat → Bool)
    (hgh : ∀ w, w ≠ v → g w = h w) (a : Bool) :
    L.foldl (fun acc w => acc ^^ g w) a =
      (L.foldl (fun acc w => acc ^^ h w) a ^^ (g v ^^ h v)) := by
  induction L generalizing a with
  | nil => exact absurd hv List.not_mem_nil
  | cons w L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.foldl_cons]
    by_cases hwv : w = v
    · subst hwv
      rw [xfold_congr L g h (fun u hu => hgh u (fun h' => hL.1 (h' ▸ hu)))]
      have : (a ^^ g w) = ((g w ^^ h w) ^^ (a ^^ h w)) := by
        cases a <;> cases g w <;> cases h w <;> rfl
      rw [this, xfold_xor]
      cases g w <;> cases h w <;> simp
    · have hv' : v ∈ L := by
        rcases List.mem_cons.mp hv with h' | h'
        · exact absurd h'.symm hwv
        · exact h'
      rw [ih hL.2 hv', hgh w hwv]

theorem parity84_congr {m m' x x' : Nat}
    (h : ∀ v, v < 84 → (m.testBit v && x.testBit v) = (m'.testBit v && x'.testBit v)) :
    parity84 m x = parity84 m' x' := by
  unfold parity84
  exact xfold_congr _ _ _ (fun w hw => h w (List.mem_range.mp hw)) _

theorem parity84_zero (m : Nat) : parity84 m 0 = false := by
  unfold parity84
  rw [xfold_congr (List.range 84) _ (fun _ => false) (fun w _ => by simp)]
  generalize List.range 84 = L
  induction L with
  | nil => rfl
  | cons w L ih => rw [List.foldl_cons, Bool.xor_false]; exact ih

theorem parity84_flip {m x x' v : Nat} (hv : v < 84)
    (hne : ∀ w, w ≠ v → x'.testBit w = x.testBit w) (hflip : x'.testBit v = !x.testBit v) :
    parity84 m x' = (parity84 m x ^^ m.testBit v) := by
  unfold parity84
  rw [xfold_flip (List.range 84) List.nodup_range v (List.mem_range.mpr hv)
    (fun w => m.testBit w && x'.testBit w) (fun w => m.testBit w && x.testBit w)
    (fun w hw => by simp only [hne w hw]) false]
  congr 1
  rw [hflip]
  cases m.testBit v <;> cases x.testBit v <;> rfl

/-- Status of the equation with code `c` on the bit-vector `x`: `true` iff it is satisfied. -/
def st (c x : Nat) : Bool := !(parity84 c x ^^ c.testBit 100)

theorem st_zero (c : Nat) : st c 0 = !c.testBit 100 := by
  simp [st, parity84_zero]

theorem st_flip {c x x' v : Nat} (hv : v < 84) (hne : ∀ w, w ≠ v → x'.testBit w = x.testBit w)
    (hflip : x'.testBit v = !x.testBit v) : st c x' = (st c x ^^ c.testBit v) := by
  unfold st
  rw [parity84_flip hv hne hflip]
  cases parity84 c x <;> cases c.testBit v <;> cases c.testBit 100 <;> rfl

theorem st_congr {c x x' : Nat}
    (h : ∀ v, v < 84 → c.testBit v = true → x.testBit v = x'.testBit v) : st c x = st c x' := by
  unfold st
  rw [parity84_congr (m' := c) (x' := x')]
  intro v hv
  cases hc : c.testBit v
  · rfl
  · rw [h v hv hc]

theorem st_code (q : Eqn) (hq : ∀ i ∈ q.tog, i < 84) (x : Nat) :
    st (Eqn.code q) x = !(q.eval x) := by
  unfold st
  rw [Eqn.code_testBit_100 q hq, Eqn.eval_eq_parity q hq x]
  rw [parity84_congr (m' := q.mask) (x' := x)
    (fun v hv => by rw [Eqn.code_testBit_lt q hq v (by omega)])]

theorem testBit_one_shiftLeft (v w : Nat) : (1 <<< v).testBit w = decide (v = w) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- A set bit of the toggle mask is a toggle. -/
theorem mask_mem (q : Eqn) (v : Nat) (h : q.mask.testBit v = true) : v ∈ q.tog := by
  unfold Eqn.mask at h
  suffices H : ∀ (L : List Nat) (m : Nat),
      (L.foldl (fun m i => m ^^^ (1 <<< i)) m).testBit v = true → m.testBit v = true ∨ v ∈ L by
    rcases H _ _ h with h0 | h0
    · simp at h0
    · exact h0
  intro L
  induction L with
  | nil => intro m hm; exact Or.inl hm
  | cons i L ih =>
    intro m hm
    rw [List.foldl_cons] at hm
    rcases ih _ hm with h1 | h1
    · rw [Nat.testBit_xor, testBit_one_shiftLeft] at h1
      by_cases hiv : i = v
      · exact Or.inr (hiv ▸ List.mem_cons_self)
      · left
        simpa [hiv] using h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-! ### Variables of the instances -/

/-- A variable index of labels `≤ n`: a sorted triple or a sorted pair. -/
def VarOK (n i : Nat) : Prop :=
  (∃ a b c, a < b ∧ b < c ∧ c ≤ n ∧ i = triIdx a b c) ∨ (∃ a b, a < b ∧ b ≤ n ∧ i = vE a b)

/-- All toggles of the equation are variables of labels `≤ n`. -/
def EqOK (n : Nat) (q : Eqn) : Prop := ∀ i ∈ q.tog, VarOK n i

theorem eqOK_add_iff {n : Nat} {p q : Eqn} : EqOK n (Eqn.add p q) ↔ EqOK n p ∧ EqOK n q := by
  simp only [EqOK, Eqn.add, List.mem_append]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨hp, hq⟩ i (hi | hi)
    exacts [hp i hi, hq i hi]

theorem eqOK_one_iff {n : Nat} : EqOK n Eqn.one ↔ True := by
  simp [EqOK, Eqn.one]

theorem eqOK_zero {n : Nat} : EqOK n Eqn.zero := by
  simp [EqOK, Eqn.zero]

theorem eqOK_X_iff {n a b c : Nat} : EqOK n (Eqn.X a b c) ↔ VarOK n (xT a b c).1 := by
  simp [EqOK, Eqn.X]

theorem eqOK_E_iff {n a b : Nat} :
    EqOK n (Eqn.E a b) ↔ VarOK n (if a < b then vE a b else vE b a) := by
  simp [EqOK, Eqn.E]

theorem varOK_xT {n a b c : Nat} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : VarOK n (xT a b c).1 := by
  unfold xT
  split_ifs <;> left
  · exact ⟨a, b, c, by omega, by omega, by omega, rfl⟩
  · exact ⟨a, c, b, by omega, by omega, by omega, rfl⟩
  · exact ⟨c, a, b, by omega, by omega, by omega, rfl⟩
  · exact ⟨b, a, c, by omega, by omega, by omega, rfl⟩
  · exact ⟨b, c, a, by omega, by omega, by omega, rfl⟩
  · exact ⟨c, b, a, by omega, by omega, by omega, rfl⟩

theorem varOK_E {n a b : Nat} (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b) :
    VarOK n (if a < b then vE a b else vE b a) := by
  split_ifs <;> right
  · exact ⟨a, b, by omega, by omega, rfl⟩
  · exact ⟨b, a, by omega, by omega, rfl⟩

theorem gpEqs_ok {n a b c d e : Nat} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n)
    (he : e ≤ n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ∀ q ∈ gpEqs a b c d e, EqOK n q := by
  have h1 := varOK_xT ha hb hc hab hac hbc
  have h2 := varOK_xT ha hd he had hae hde
  have h3 := varOK_xT ha hb hd hab had hbd
  have h4 := varOK_xT ha hc he hac hae hce
  have h5 := varOK_xT ha hb he hab hae hbe
  have h6 := varOK_xT ha hc hd hac had hcd
  simp only [gpEqs, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    eqOK_add_iff, eqOK_one_iff, eqOK_X_iff, and_true]
  exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩⟩

theorem circBase_ok {n v0 v1 v2 v3 : Nat} (h0 : v0 ≤ n) (h1 : v1 ≤ n) (h2 : v2 ≤ n) (h3 : v3 ≤ n)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (h23 : v2 ≠ v3) : ∀ q ∈ circBase v0 v1 v2 v3, EqOK n q := by
  have x0 := varOK_xT h1 h2 h3 h12 h13 h23
  have x1 := varOK_xT h0 h2 h3 h02 h03 h23
  have x2 := varOK_xT h0 h1 h3 h01 h03 h13
  have x3 := varOK_xT h0 h1 h2 h01 h02 h12
  have e01 := varOK_E h0 h1 h01
  have e02 := varOK_E h0 h2 h02
  have e03 := varOK_E h0 h3 h03
  have e12 := varOK_E h1 h2 h12
  have e13 := varOK_E h1 h3 h13
  have e23 := varOK_E h2 h3 h23
  simp only [circBase, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    eqOK_add_iff, eqOK_one_iff, eqOK_X_iff, eqOK_E_iff, and_true, true_and]
  exact ⟨⟨⟨e01, x0⟩, x1⟩, ⟨⟨e02, x0⟩, x2⟩, ⟨⟨e03, x0⟩, x3⟩, ⟨⟨e12, x1⟩, x2⟩, ⟨⟨e13, x1⟩, x3⟩,
    ⟨⟨e23, x2⟩, x3⟩⟩

theorem forbEqs_ok {n r s i j k : Nat} (hr : r ≤ n) (hs : s ≤ n) (hi : i ≤ n) (hj : j ≤ n)
    (hk : k ≤ n) (hrs : r ≠ s) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (hsi : s ≠ i)
    (hsj : s ≠ j) (hsk : s ≠ k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ q ∈ forbEqs r s i j k, EqOK n q := by
  have xrsi := varOK_xT hr hs hi hrs hri hsi
  have xrsj := varOK_xT hr hs hj hrs hrj hsj
  have xrsk := varOK_xT hr hs hk hrs hrk hsk
  have xrjk := varOK_xT hr hj hk hrj hrk hjk
  have xsjk := varOK_xT hs hj hk hsj hsk hjk
  have xrij := varOK_xT hr hi hj hri hrj hij
  have xsij := varOK_xT hs hi hj hsi hsj hij
  have xrik := varOK_xT hr hi hk hri hrk hik
  have xsik := varOK_xT hs hi hk hsi hsk hik
  have ers := varOK_E hr hs hrs
  have eri := varOK_E hr hi hri
  have erj := varOK_E hr hj hrj
  have erk := varOK_E hr hk hrk
  have esi := varOK_E hs hi hsi
  have esj := varOK_E hs hj hsj
  have esk := varOK_E hs hk hsk
  have eij := varOK_E hi hj hij
  have eik := varOK_E hi hk hik
  simp only [forbEqs, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    eqOK_add_iff, eqOK_one_iff, eqOK_X_iff, eqOK_E_iff, and_true, true_and]
  simp only [xrsi, xrsj, xrsk, xrjk, xsjk, xrij, xsij, xrik, xsik, ers, eri, erj, erk, esi, esj,
    esk, eij, eik, and_self]

theorem pad8_ok {n : Nat} {l : List Eqn} (hl : ∀ q ∈ l, EqOK n q) : ∀ q ∈ pad8 l, EqOK n q := by
  intro q hq
  rw [pad8, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hl q hq
  · rw [List.eq_of_mem_replicate hq]
    exact eqOK_zero

theorem inst_eqns_ok {n : Nat} {inst : Inst} (hwf : inst.wfB n = true) :
    ∀ q ∈ inst.eqns, EqOK n q := by
  have hw : (∀ x ∈ inst.labs, x ≤ n) ∧ inst.labs.Nodup := by
    unfold Inst.wfB at hwf
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
    exact hwf.1
  obtain ⟨hle, hnd⟩ := hw
  cases inst with
  | gp a b c d e =>
    simp only [Inst.labs, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true] at hle
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, or_false,
      not_false_eq_true, and_true, List.nodup_nil] at hnd
    obtain ⟨ha, hb, hc, hd, he⟩ := hle
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩ := hnd
    exact pad8_ok (gpEqs_ok ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde)
  | circ v0 v1 v2 v3 p =>
    simp only [Inst.labs, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true] at hle
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, or_false,
      not_false_eq_true, and_true, List.nodup_nil] at hnd
    obtain ⟨h0, h1, h2, h3⟩ := hle
    obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := hnd
    have hb := circBase_ok h0 h1 h2 h3 h01 h02 h03 h12 h13 h23
    apply pad8_ok
    intro q hq
    simp only [circEqs, List.mem_map] at hq
    obtain ⟨⟨q0, t⟩, hmem, rfl⟩ := hq
    exact hb q0 (List.of_mem_zip hmem).1
  | forb r s i j k =>
    simp only [Inst.labs, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true] at hle
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, or_false,
      not_false_eq_true, and_true, List.nodup_nil] at hnd
    obtain ⟨hr, hs, hi, hj, hk⟩ := hle
    obtain ⟨⟨hrs, hri, hrj, hrk⟩, ⟨hsi, hsj, hsk⟩, ⟨hij, hik⟩, hjk⟩ := hnd
    exact pad8_ok (forbEqs_ok hr hs hi hj hk hrs hri hrj hrk hsi hsj hsk hij hik hjk)

/-! ### The variable lists `orderOf n` and `baseVars n` -/

/-- Duplicate-freeness of a list of bit indices, checked with a bit mask of the indices seen. -/
def nodupB : List Nat → Nat → Bool
  | [], _ => true
  | v :: l, m => !(m.testBit v) && nodupB l (m ||| (1 <<< v))

theorem nodupB_sound : ∀ (l : List Nat) (m : Nat), nodupB l m = true →
    l.Nodup ∧ ∀ v ∈ l, m.testBit v = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | v :: l, m, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hnd, hm⟩ := nodupB_sound l _ h2
    refine ⟨List.nodup_cons.mpr ⟨fun hv => ?_, hnd⟩, ?_⟩
    · have := hm v hv
      rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_true rfl, Bool.or_true] at this
      exact absurd this (by decide)
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h1
      · have := hm w hw
        simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

/-- Small kernel computation (linear in the list lengths, `n ≤ 7`). -/
theorem lists_okB : ∀ n, n < 8 → (nodupB (orderOf n) 0 && nodupB (baseVars n) 0 &&
    (orderOf n).all (· < 84) && (baseVars n).all (· < 84)) = true := by
  decide +kernel

theorem lists_ok (n : Nat) (hn : n < 8) : (orderOf n).Nodup ∧ (baseVars n).Nodup ∧
    (∀ v ∈ orderOf n, v < 84) ∧ ∀ v ∈ baseVars n, v < 84 := by
  have h := lists_okB n hn
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨(nodupB_sound _ _ h1).1, (nodupB_sound _ _ h2).1, h3, h4⟩

theorem mem_orderOf_tri {a b n : Nat} (hab : a < b) (hbn : b < n) : triIdx a b n ∈ orderOf n := by
  simp only [orderOf, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  exact ⟨b, hbn, Or.inr ⟨a, hab, rfl⟩⟩

theorem mem_orderOf_vE {a n : Nat} (han : a < n) : vE a n ∈ orderOf n := by
  simp only [orderOf, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  exact ⟨a, han, Or.inl rfl⟩

theorem mem_baseVars_tri {a b c n : Nat} (hab : a < b) (hbc : b < c) (hcn : c < n) :
    triIdx a b c ∈ baseVars n := by
  simp only [baseVars, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  exact Or.inl ⟨c, hcn, b, hbc, a, hab, rfl⟩

theorem mem_baseVars_vE {a b n : Nat} (hab : a < b) (hbn : b < n) : vE a b ∈ baseVars n := by
  simp only [baseVars, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  exact Or.inr ⟨b, hbn, a, hab, rfl⟩

theorem varOK_mem {n i : Nat} (h : VarOK n i) : i ∈ baseVars n ∨ i ∈ orderOf n := by
  rcases h with ⟨a, b, c, hab, hbc, hcn, rfl⟩ | ⟨a, b, hab, hbn, rfl⟩
  · rcases Nat.lt_or_ge c n with hc | hc
    · exact Or.inl (mem_baseVars_tri hab hbc hc)
    · have : c = n := by omega
      subst this
      exact Or.inr (mem_orderOf_tri hab hbc)
  · rcases Nat.lt_or_ge b n with hb | hb
    · exact Or.inl (mem_baseVars_vE hab hb)
    · have : b = n := by omega
      subst this
      exact Or.inr (mem_orderOf_vE hab)

theorem varOK_lt {n i : Nat} (hn : n ≤ 7) (h : VarOK n i) : i < 84 := by
  obtain ⟨-, -, ho, hb⟩ := lists_ok n (by omega)
  rcases varOK_mem h with h' | h'
  · exact hb i h'
  · exact ho i h'

theorem getElem_not_mem_take {l : List Nat} (hl : l.Nodup) {d : Nat} (hd : d < l.length) :
    l[d] ∉ l.take d := by
  intro hm
  obtain ⟨j, hj, hjd⟩ := List.mem_take_iff_getElem.mp hm
  have := (List.getElem_inj hl).mp hjd
  omega

/-! ### The search -/

/-- `x` is the bit-vector of the true path at depth `d`. -/
def PathX (n y xs d x : Nat) : Prop :=
  ∀ w, x.testBit w = (y.testBit w || (decide (w ∈ (orderOf n).take d) && xs.testBit w))

/-- The packed state `q` records the status of every equation on `x`. -/
def Plane (rows : List (List Nat)) (q x : Nat) : Prop :=
  ∀ e, e < 8 → ∀ s, s < rows.length → q.testBit (e * rows.length + s) = st (codeAt rows s e) x

theorem dfsM_nil (S q mq x : Nat) (acc : List Nat) : dfsM S [] q mq x acc = x :: acc := rfl

theorem dfsM_cons (S a b c : Nat) (ts : List (Nat × Nat × Nat)) (q mq x : Nat)
    (acc : List Nat) :
    dfsM S ((a, b, c) :: ts) q mq x acc =
      (bif Nat.ble 1 (mq &&& c) then
        (bif Nat.ble 1 (red S (q ^^^ b) &&& c) then acc
         else dfsM S ts (q ^^^ b) (red S (q ^^^ b)) (x ||| a) acc)
       else dfsM S ts q mq x
        (bif Nat.ble 1 (red S (q ^^^ b) &&& c) then acc
         else dfsM S ts (q ^^^ b) (red S (q ^^^ b)) (x ||| a) acc)) := rfl

theorem mem_cond {b : Bool} {l₁ l₂ : List Nat} {a : Nat} (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) :
    a ∈ (bif b then l₁ else l₂) := by
  cases b
  · exact h₂
  · exact h₁

/-- The accumulator only grows. -/
theorem dfsM_mono (S : Nat) : ∀ (ts : List (Nat × Nat × Nat)) (q mq x : Nat) (acc : List Nat),
    ∀ a ∈ acc, a ∈ dfsM S ts q mq x acc := by
  intro ts
  induction ts with
  | nil => intro q mq x acc a ha; exact List.mem_cons_of_mem _ ha
  | cons t ts ih =>
    intro q mq x acc a ha
    obtain ⟨t1, t2, t3⟩ := t
    rw [dfsM_cons]
    have h1 := mem_cond (b := Nat.ble 1 (red S (q ^^^ t2) &&& t3)) ha
      (ih (q ^^^ t2) (red S (q ^^^ t2)) (x ||| t1) acc a ha)
    exact mem_cond h1 (ih q mq x _ a h1)

/-- All hypotheses of the main theorem, with a representation `xs` of `D` on all labels. -/
structure Setup (n : Nat) (insts : List Inst) (lv : Lv) (D : SD) (y xs : Nat) : Prop where
  hn : n ≤ 7
  hrows : lv.rows = insts.map Inst.row
  hcols : lv.cols = (List.range 84).map (colSpec lv.rows)
  hkp : lv.kp = kpSpec lv.rows
  hdone : lv.done = doneSpec n lv.rows
  hS : lv.rows.length ≤ 598
  hwf : ∀ i ∈ insts, i.wfB n = true
  hD : D.Valid8
  hy : AgreeJ n D y
  hy0 : ∀ v ∈ orderOf n, y.testBit v = false
  hxs : AgreeJ 8 D xs

section
variable {n : Nat} {insts : List Inst} {lv : Lv} {D : SD} {y xs : Nat}

theorem Setup.len (H : Setup n insts lv D y xs) : lv.rows.length = insts.length := by
  rw [H.hrows, List.length_map]

theorem Setup.tog_lt (H : Setup n insts lv D y xs) {inst : Inst} (hi : inst ∈ insts) :
    ∀ q ∈ inst.eqns, ∀ i ∈ q.tog, i < 84 :=
  fun q hq i hi' => varOK_lt H.hn (inst_eqns_ok (H.hwf inst hi) q hq i hi')

theorem Setup.code_eq (H : Setup n insts lv D y xs) {s : Nat} (hs : s < insts.length) {e : Nat}
    (he : e < insts[s].eqns.length) : codeAt lv.rows s e = Eqn.code (insts[s].eqns[e]) := by
  unfold codeAt
  rw [H.hrows]
  simp [List.getElem?_eq_getElem hs, Inst.row, List.getElem?_eq_getElem he]

/-- A variable occurring in an equation code of a system is a variable of labels `≤ n`. -/
theorem Setup.code_var (H : Setup n insts lv D y xs) {s e v : Nat} (hs : s < lv.rows.length)
    (he : e < 8) (hv : v < 84) (hc : (codeAt lv.rows s e).testBit v = true) : VarOK n v := by
  have hs' : s < insts.length := H.len ▸ hs
  have he' : e < insts[s].eqns.length := by rw [Inst.eqns_length]; exact he
  have hmem : insts[s] ∈ insts := List.getElem_mem hs'
  rw [H.code_eq hs' he', Eqn.code_testBit_lt _ (H.tog_lt hmem _ (List.getElem_mem he')) v
    (by omega)] at hc
  exact inst_eqns_ok (H.hwf _ hmem) _ (List.getElem_mem he') v (mask_mem _ v hc)

theorem Setup.codes_lt (H : Setup n insts lv D y xs) : ∀ r ∈ lv.rows, ∀ c ∈ r, c < 2 ^ 101 := by
  intro r hr c hc
  rw [H.hrows, List.mem_map] at hr
  obtain ⟨inst, hinst, rfl⟩ := hr
  simp only [Inst.row, List.mem_map] at hc
  obtain ⟨q, hq, rfl⟩ := hc
  have htog := H.tog_lt hinst q hq
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  unfold Eqn.code
  rw [Nat.testBit_or]
  have h1 : q.mask.testBit i = false := by
    cases hm : q.mask.testBit i
    · rfl
    · have := htog i (mask_mem q i hm)
      omega
  rw [h1]
  cases q.c
  · simp
  · rw [cond_true, testBit_one_shiftLeft, decide_eq_false (by omega)]
    rfl

theorem Setup.rows_len (H : Setup n insts lv D y xs) : ∀ r ∈ lv.rows, r.length = 8 := by
  intro r hr
  rw [H.hrows, List.mem_map] at hr
  obtain ⟨inst, -, rfl⟩ := hr
  rw [Inst.row, List.length_map, Inst.eqns_length]

theorem Setup.plane_kp (H : Setup n insts lv D y xs) : Plane lv.rows (kpSpec lv.rows) 0 := by
  intro e he s hs
  rw [kpSpec_testBit lv.rows H.rows_len e s he hs, st_zero]

theorem Setup.cols_getD (H : Setup n insts lv D y xs) {v : Nat} (hv : v < 84) :
    lv.cols.getD v 0 = colSpec lv.rows v := by
  rw [H.hcols]
  simp [List.getElem?_range hv]

/-- On the variables of labels `≤ n` that are already assigned, the true path agrees with `xs`. -/
theorem Setup.path_agree (H : Setup n insts lv D y xs) {d x : Nat} (hx : PathX n y xs d x)
    {v : Nat} (hv : VarOK n v) (hd : v ∈ orderOf n → v ∈ (orderOf n).take d) :
    x.testBit v = xs.testBit v := by
  have hn := H.hn
  rw [hx v]
  rcases hv with ⟨a, b, c, hab, hbc, hcn, rfl⟩ | ⟨a, b, hab, hbn, rfl⟩
  · rcases Nat.lt_or_ge c n with hc | hc
    · have h1 := H.hy.1 ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ (Fin.mk_lt_mk.mpr hab)
        (Fin.mk_lt_mk.mpr hbc) hc
      have h2 := H.hxs.1 ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ (Fin.mk_lt_mk.mpr hab)
        (Fin.mk_lt_mk.mpr hbc) (by show c < 8; omega)
      simp only at h1 h2
      rw [h1, h2]
      cases D.neg3 _ _ _ <;> simp
    · have hc' : c = n := by omega
      subst hc'
      have hm := mem_orderOf_tri hab hbc
      rw [H.hy0 _ hm, decide_eq_true (hd hm)]
      simp
  · rcases Nat.lt_or_ge b n with hb | hb
    · have h1 := H.hy.2 ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.mk_lt_mk.mpr hab) hb
      have h2 := H.hxs.2 ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.mk_lt_mk.mpr hab)
        (by show b < 8; omega)
      simp only at h1 h2
      rw [h1, h2]
      cases D.neg2 _ _ <;> simp
    · have hb' : b = n := by omega
      subst hb'
      have hm := mem_orderOf_vE hab
      rw [H.hy0 _ hm, decide_eq_true (hd hm)]
      simp

/-- A node of the true path is never pruned. -/
theorem Setup.no_prune (H : Setup n insts lv D y xs) {d q x : Nat} (hx : PathX n y xs d x)
    (hq : Plane lv.rows q x) : red lv.rows.length q &&& doneAt n lv.rows d = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit, Nat.testBit_and]
  cases hred : (red lv.rows.length q).testBit i
  · rfl
  cases hdn : (doneAt n lv.rows d).testBit i
  · rfl
  exfalso
  have hi : i < lv.rows.length := by
    rcases Nat.lt_or_ge i lv.rows.length with h' | h'
    · exact h'
    · rw [doneAt_testBit_ge n lv.rows d i h'] at hdn
      exact absurd hdn (by decide)
  have hdone := (doneAt_testBit n lv.rows H.rows_len d i hi).mp hdn
  have hall := (red_testBit _ _ _ hi).mp hred
  have hi' : i < insts.length := H.len ▸ hi
  have hmem : insts[i] ∈ insts := List.getElem_mem hi'
  have hwf := H.hwf _ hmem
  apply Inst.sound n H.hn D H.hD.1 xs H.hxs insts[i] hwf _
    (Inst.holds_of_valid n H.hn insts[i] hwf D H.hD)
  intro q' hq'
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hq'
  have he8 : e < 8 := by rwa [Inst.eqns_length] at he
  have hcode := H.code_eq hi' he
  have hsat := hall e he8
  rw [hq e he8 i hi] at hsat
  have hst : st (codeAt lv.rows i e) x = st (codeAt lv.rows i e) xs := by
    apply st_congr
    intro v hv hcv
    exact H.path_agree hx (H.code_var hi he8 hv hcv) (fun hm => hdone v ⟨e, he8, hcv⟩ hm)
  rw [hst, hcode, st_code _ (H.tog_lt hmem _ (List.getElem_mem he))] at hsat
  simpa using hsat

theorem Setup.plane_flip (H : Setup n insts lv D y xs) {q x x' v : Nat} (hv : v < 84)
    (hq : Plane lv.rows q x) (hne : ∀ w, w ≠ v → x'.testBit w = x.testBit w)
    (hflip : x'.testBit v = !x.testBit v) : Plane lv.rows (q ^^^ colSpec lv.rows v) x' := by
  intro e he s hs
  rw [Nat.testBit_xor, hq e he s hs, colSpec_testBit lv.rows H.hS H.codes_lt v hv e s he hs,
    st_flip hv hne hflip]

theorem Setup.plane_fold (H : Setup n insts lv D y xs) (L : List Nat) (hL : ∀ v ∈ L, v < 84) :
    ∀ q z, Plane lv.rows q z →
      Plane lv.rows
        (L.foldl (fun q v => bif Nat.testBit y v then Nat.xor q (lv.cols.getD v 0) else q) q)
        (L.foldl (fun z v => bif Nat.testBit y v then z ^^^ (1 <<< v) else z) z) := by
  induction L with
  | nil => intro q z h; exact h
  | cons v L ih =>
    intro q z h
    simp only [List.foldl_cons]
    apply ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
    have hv := hL v List.mem_cons_self
    cases hyv : y.testBit v
    · exact h
    · simp only [cond_true]
      rw [Nat.xor_eq, H.cols_getD hv]
      refine H.plane_flip hv h (fun w hw => ?_) ?_
      · rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_false (Ne.symm hw), Bool.xor_false]
      · rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_true rfl, Bool.xor_true]

theorem zfold_testBit (y : Nat) (L : List Nat) (hL : L.Nodup) :
    ∀ z w, (L.foldl (fun z v => bif Nat.testBit y v then z ^^^ (1 <<< v) else z) z).testBit w =
      (z.testBit w ^^ (decide (w ∈ L) && y.testBit w)) := by
  induction L with
  | nil => intro z w; simp
  | cons v L ih =>
    intro z w
    rw [List.nodup_cons] at hL
    rw [List.foldl_cons, ih hL.2]
    by_cases hw : w = v
    · subst hw
      cases y.testBit w
      · simp only [cond_false, Bool.and_false]
      · simp only [cond_true, Nat.testBit_xor, testBit_one_shiftLeft, Bool.and_true,
          decide_eq_false hL.1, decide_eq_true (List.mem_cons_self (a := w) (l := L)),
          decide_true, Bool.xor_false]
    · have hm : decide (w ∈ v :: L) = decide (w ∈ L) := by
        simp only [List.mem_cons, hw, false_or]
      rw [hm]
      cases y.testBit v
      · simp only [cond_false]
      · simp only [cond_true, Nat.testBit_xor, testBit_one_shiftLeft,
          decide_eq_false (Ne.symm hw), Bool.xor_false]

theorem Setup.plane_init (H : Setup n insts lv D y xs) :
    Plane lv.rows
      ((baseVars n).foldl (fun q v => bif Nat.testBit y v then Nat.xor q (lv.cols.getD v 0) else q)
        lv.kp) y := by
  obtain ⟨-, hnd, -, hbd⟩ := lists_ok n (by have := H.hn; omega)
  have h0 : Plane lv.rows lv.kp 0 := by
    rw [H.hkp]
    exact H.plane_kp
  have h1 := H.plane_fold (baseVars n) hbd lv.kp 0 h0
  intro e he s hs
  rw [h1 e he s hs]
  apply st_congr
  intro v hv hcv
  rw [zfold_testBit y _ hnd, Nat.zero_testBit, Bool.false_xor]
  rcases varOK_mem (H.code_var hs he hv hcv) with hb | ho
  · simp [hb]
  · simp [H.hy0 v ho]

theorem Setup.steps_length (H : Setup n insts lv D y xs) :
    (mkSteps (orderOf n) lv.cols lv.done).length = (orderOf n).length := by
  simp [mkSteps, H.hdone, doneSpec]

theorem Setup.steps_drop (H : Setup n insts lv D y xs) {d : Nat} (hd : d < (orderOf n).length) :
    (mkSteps (orderOf n) lv.cols lv.done).drop d =
      (1 <<< (orderOf n)[d], colSpec lv.rows (orderOf n)[d], doneAt n lv.rows (d + 1)) ::
        (mkSteps (orderOf n) lv.cols lv.done).drop (d + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [H.steps_length]; exact hd)]
  congr 1
  have hv : (orderOf n)[d] < 84 :=
    (lists_ok n (by have := H.hn; omega)).2.2.1 _ (List.getElem_mem hd)
  simp [mkSteps, H.hdone, doneSpec, H.hcols, List.getElem?_range hv]

theorem pathX_succ_false {n y xs d x : Nat} (hd : d < (orderOf n).length) (hx : PathX n y xs d x)
    (hv : xs.testBit (orderOf n)[d] = false) : PathX n y xs (d + 1) x := by
  intro w
  rw [hx w, List.take_succ_eq_append_getElem hd]
  simp only [List.mem_append, List.mem_singleton]
  by_cases hw : w = (orderOf n)[d]
  · subst hw
    simp [hv]
  · simp [hw]

theorem pathX_succ_true {n y xs d x : Nat} (hd : d < (orderOf n).length) (hx : PathX n y xs d x)
    (hv : xs.testBit (orderOf n)[d] = true) :
    PathX n y xs (d + 1) (x ||| (1 <<< (orderOf n)[d])) := by
  intro w
  rw [Nat.testBit_or, hx w, List.take_succ_eq_append_getElem hd, testBit_one_shiftLeft]
  simp only [List.mem_append, List.mem_singleton]
  by_cases hw : w = (orderOf n)[d]
  · subst hw
    simp [hv]
  · simp [hw, Ne.symm hw]

/-- The search started on the true path at depth `d` returns the leaf of the true path. -/
theorem Setup.dfs (H : Setup n insts lv D y xs) :
    ∀ (ts : List (Nat × Nat × Nat)) (d q x : Nat) (acc : List Nat),
      (mkSteps (orderOf n) lv.cols lv.done).drop d = ts → PathX n y xs d x → Plane lv.rows q x →
      ∃ x' ∈ dfsM lv.rows.length ts q (red lv.rows.length q) x acc,
        PathX n y xs (orderOf n).length x' := by
  intro ts
  induction ts with
  | nil =>
    intro d q x acc hts hx _
    refine ⟨x, List.mem_cons_self, ?_⟩
    have hlen : (orderOf n).length ≤ d := by
      have := List.drop_eq_nil_iff.mp hts
      rwa [H.steps_length] at this
    intro w
    rw [hx w, List.take_of_length_le hlen, List.take_length]
  | cons t ts ih =>
    intro d q x acc hts hx hq
    have hd : d < (orderOf n).length := by
      rcases Nat.lt_or_ge d (orderOf n).length with h' | h'
      · exact h'
      · have h'' : (mkSteps (orderOf n) lv.cols lv.done).length ≤ d := by
          rw [H.steps_length]
          exact h'
        rw [List.drop_eq_nil_iff.mpr h''] at hts
        exact absurd hts.symm (List.cons_ne_nil _ _)
    rw [H.steps_drop hd] at hts
    obtain ⟨rfl, hts'⟩ := List.cons.inj hts
    obtain ⟨hnd, -, hord, -⟩ := lists_ok n (by have := H.hn; omega)
    have hvmem : (orderOf n)[d] ∈ orderOf n := List.getElem_mem hd
    have hv84 : (orderOf n)[d] < 84 := hord _ hvmem
    rw [dfsM_cons]
    cases hxv : xs.testBit (orderOf n)[d]
    · -- the variable is `false` in `D`: follow the second child
      have hx' := pathX_succ_false hd hx hxv
      rw [H.no_prune hx' hq]
      exact ih (d + 1) q x _ hts' hx' hq
    · -- the variable is `true` in `D`: follow the first child
      have hx' := pathX_succ_true hd hx hxv
      have hx0 : x.testBit (orderOf n)[d] = false := by
        rw [hx, H.hy0 _ hvmem, decide_eq_false (getElem_not_mem_take hnd hd)]
        rfl
      have hq' : Plane lv.rows (q ^^^ colSpec lv.rows (orderOf n)[d])
          (x ||| (1 <<< (orderOf n)[d])) := by
        refine H.plane_flip hv84 hq (fun w hw => ?_) ?_
        · rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_false (Ne.symm hw), Bool.or_false]
        · rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_true rfl, hx0]
          rfl
      obtain ⟨x', hx'mem, hx'p⟩ := ih (d + 1) _ _ acc hts' hx' hq'
      refine ⟨x', ?_, hx'p⟩
      rw [H.no_prune hx' hq']
      exact mem_cond hx'mem (dfsM_mono _ _ _ _ _ _ _ hx'mem)

theorem Setup.agree_final (H : Setup n insts lv D y xs) {x : Nat}
    (hx : PathX n y xs (orderOf n).length x) : AgreeJ (n + 1) D x := by
  have hd : ∀ v, v ∈ orderOf n → v ∈ (orderOf n).take (orderOf n).length := by
    intro v hv
    rwa [List.take_length]
  constructor
  · intro a b c hab hbc hc
    rw [H.path_agree hx (Or.inl ⟨a, b, c, hab, hbc, by omega, rfl⟩) (hd _),
      H.hxs.1 a b c hab hbc c.isLt]
  · intro a b hab hb
    rw [H.path_agree hx (Or.inr ⟨a, b, hab, by omega, rfl⟩) (hd _), H.hxs.2 a b hab b.isLt]

end

end KDfs

theorem Kc.leaves_complete (n : Nat) (hn : n ≤ 7) (insts : List Kc.Inst) (lv : Kc.Lv)
    (hlv : lv.Valid n insts) (D : SD) (hD : D.Valid8) (y : Nat) (hy : AgreeJ n D y)
    (hy0 : Nat.land y (Kc.newMask n) = 0) :
    ∃ x ∈ Kc.leavesM n lv y, AgreeJ (n + 1) D x := by
  obtain ⟨xs, hxs⟩ := exists_agreeJ D
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlv
  have hy0' : ∀ v ∈ orderOf n, y.testBit v = false := by
    intro v hv
    have := congrArg (fun z => z.testBit v) hy0
    simp only [Nat.land_eq, Nat.testBit_and, testBit_newMask, Nat.zero_testBit] at this
    simpa [hv] using this
  have H : KDfs.Setup n insts lv D y xs := ⟨hn, h1, h2, h3, h4, h5, h6, hD, hy, hy0', hxs⟩
  obtain ⟨x, hx, hpx⟩ := H.dfs _ 0 _ y [] rfl
    (fun w => by simp) H.plane_init
  exact ⟨x, hx, H.agree_final hpx⟩

end Results.EightEquidistantLines
