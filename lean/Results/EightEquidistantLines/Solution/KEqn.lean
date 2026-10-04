import Results.EightEquidistantLines.Solution.Spec
import Results.EightEquidistantLines.Solution.KComp

/-!
# Soundness of the instance equations

`AgreeJ n D x` : the joint bit-vector `x` (see `KComp`) agrees with the sign data `D` on all
variables of labels `< n`.  `Kc.Inst.sound` : if all (eight) equations of an instance are
satisfied by a bit-vector agreeing with a well-formed `D`, the local constraint expressed by the
instance fails for `D`.
-/

namespace Results.EightEquidistantLines

open Kc

/-- The joint bit-vector `x` agrees with `D` on the variables of labels `< n`. -/
def AgreeJ (n : Nat) (D : SD) (x : Nat) : Prop :=
  (∀ a b c : Fin 8, a < b → b < c → c.val < n → x.testBit (triIdx a b c) = D.neg3 a b c) ∧
  (∀ a b : Fin 8, a < b → b.val < n → x.testBit (vE a b) = D.neg2 a b)

namespace KEqn

/-- Any finite prefix of bits is realized by a natural number. -/
theorem exists_bits (f : Nat → Bool) : ∀ N : Nat, ∃ x : Nat, x < 2 ^ N ∧ ∀ i < N, x.testBit i = f i
  | 0 => ⟨0, by decide, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | N + 1 => by
    obtain ⟨x, hxN, hx⟩ := exists_bits f N
    have hpow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [Nat.pow_succ]; omega
    cases hf : f N
    · refine ⟨x, by omega, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact hx i h
      · subst h; rw [hf]; exact Nat.testBit_lt_two_pow hxN
    · refine ⟨2 ^ N + x, by omega, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · rw [Nat.testBit_two_pow_add_gt h]; exact hx i h
      · subst h; rw [hf, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hxN]; rfl

/-- The sorted triples of labels in colexicographic order (position `triIdx a b c`). -/
def trisL : List (Fin 8 × Fin 8 × Fin 8) :=
  [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3), (0, 1, 4), (0, 2, 4), (1, 2, 4), (0, 3, 4), (1, 3, 4),
   (2, 3, 4), (0, 1, 5), (0, 2, 5), (1, 2, 5), (0, 3, 5), (1, 3, 5), (2, 3, 5), (0, 4, 5), (1, 4, 5),
   (2, 4, 5), (3, 4, 5), (0, 1, 6), (0, 2, 6), (1, 2, 6), (0, 3, 6), (1, 3, 6), (2, 3, 6), (0, 4, 6),
   (1, 4, 6), (2, 4, 6), (3, 4, 6), (0, 5, 6), (1, 5, 6), (2, 5, 6), (3, 5, 6), (4, 5, 6), (0, 1, 7),
   (0, 2, 7), (1, 2, 7), (0, 3, 7), (1, 3, 7), (2, 3, 7), (0, 4, 7), (1, 4, 7), (2, 4, 7), (3, 4, 7),
   (0, 5, 7), (1, 5, 7), (2, 5, 7), (3, 5, 7), (4, 5, 7), (0, 6, 7), (1, 6, 7), (2, 6, 7), (3, 6, 7),
   (4, 6, 7), (5, 6, 7)]

/-- The sorted pairs of labels in colexicographic order (position `prIdx a b`). -/
def prsL : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3), (0, 4), (1, 4), (2, 4), (3, 4), (0, 5), (1, 5),
   (2, 5), (3, 5), (4, 5), (0, 6), (1, 6), (2, 6), (3, 6), (4, 6), (5, 6), (0, 7), (1, 7), (2, 7),
   (3, 7), (4, 7), (5, 7), (6, 7)]

theorem trisL_spec : ∀ a b c : Fin 8, a < b → b < c →
    triIdx a b c < 56 ∧ trisL.getD (triIdx a b c) (0, 0, 0) = (a, b, c) := by
  decide +kernel

theorem prsL_spec : ∀ a b : Fin 8, a < b → prIdx a b < 28 ∧ prsL.getD (prIdx a b) (0, 0) = (a, b) := by
  decide +kernel

end KEqn

/-- Every sign datum has a joint bit-vector representation. -/
theorem exists_agreeJ (D : SD) : ∃ x : Nat, AgreeJ 8 D x := by
  obtain ⟨x, -, hx⟩ := KEqn.exists_bits (fun i => if i < 56 then
      D.neg3 (KEqn.trisL.getD i (0, 0, 0)).1 (KEqn.trisL.getD i (0, 0, 0)).2.1
        (KEqn.trisL.getD i (0, 0, 0)).2.2
    else D.neg2 (KEqn.prsL.getD (i - 56) (0, 0)).1 (KEqn.prsL.getD (i - 56) (0, 0)).2) 84
  refine ⟨x, ?_, ?_⟩
  · intro a b c hab hbc _
    obtain ⟨h56, hget⟩ := KEqn.trisL_spec a b c hab hbc
    rw [hx _ (by omega), if_pos h56, hget]
  · intro a b hab _
    obtain ⟨h28, hget⟩ := KEqn.prsL_spec a b hab
    have hv : vE a b = 56 + prIdx a b := rfl
    rw [hx _ (by omega), if_neg (by omega), show vE a b - 56 = prIdx a b by omega, hget]

/-- The local constraint expressed by an instance holds for `D`. -/
def Kc.Inst.Holds (D : SD) : Kc.Inst → Prop
  | .gp a b c d e => D.GPinst (Fin.ofNat 8 a) (Fin.ofNat 8 b) (Fin.ofNat 8 c) (Fin.ofNat 8 d) (Fin.ofNat 8 e)
  | .circ v0 v1 v2 v3 _ => D.CircInst (Fin.ofNat 8 v0) (Fin.ofNat 8 v1) (Fin.ofNat 8 v2) (Fin.ofNat 8 v3)
  | .forb r s i j k => D.ForbInst (Fin.ofNat 8 r) (Fin.ofNat 8 s) (Fin.ofNat 8 i) (Fin.ofNat 8 j) (Fin.ofNat 8 k)

namespace KEqn

/-! ### Evaluation of equations -/

theorem foldl_xor (g : Nat → Bool) (l : List Nat) (a : Bool) :
    l.foldl (fun acc i => acc ^^ g i) a = (a ^^ l.foldl (fun acc i => acc ^^ g i) false) := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, Bool.xor_false]
  | cons v l ih =>
    simp only [List.foldl_cons]
    rw [ih (a ^^ g v), ih (false ^^ g v), Bool.false_xor, Bool.xor_assoc]

theorem eval_def (q : Eqn) (x : Nat) :
    q.eval x = (q.c ^^ q.tog.foldl (fun acc i => acc ^^ x.testBit i) false) :=
  foldl_xor _ _ _

theorem eval_add (p q : Eqn) (x : Nat) : (Eqn.add p q).eval x = (p.eval x ^^ q.eval x) := by
  simp only [eval_def, Eqn.add, List.foldl_append]
  rw [foldl_xor _ q.tog]
  generalize p.c = a
  generalize q.c = b
  generalize List.foldl (fun acc i => acc ^^ x.testBit i) false p.tog = c
  generalize List.foldl (fun acc i => acc ^^ x.testBit i) false q.tog = d
  revert a b c d; decide

theorem eval_X (a b c x : Nat) : (Eqn.X a b c).eval x = xBit x a b c := by
  simp only [Eqn.eval, Eqn.X, List.foldl_cons, List.foldl_nil, xBit]
  exact Bool.xor_comm _ _

theorem eval_E (a b x : Nat) : (Eqn.E a b).eval x = eBit x a b := by
  simp only [Eqn.eval, Eqn.E, List.foldl_cons, List.foldl_nil, eBit, Bool.false_xor]

theorem eval_one (x : Nat) : Eqn.one.eval x = true := rfl

theorem eval_zero (x : Nat) : Eqn.zero.eval x = false := rfl

theorem eval_mk_xor (q : Eqn) (b : Bool) (x : Nat) :
    (Eqn.mk q.tog (q.c ^^ b)).eval x = (q.eval x ^^ b) := by
  simp only [eval_def]
  generalize q.c = a
  generalize List.foldl (fun acc i => acc ^^ x.testBit i) false q.tog = c
  revert a b c; decide

theorem eq_of_xor_eq_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem eq_not_of_xor_xor_true {a b : Bool} (h : ((a ^^ b) ^^ true) = false) : a = !b := by
  revert h; cases a <;> cases b <;> decide

/-! ### Reading the sign data from an agreeing bit-vector -/

theorem nodup3 {a b c : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : [a, b, c].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨⟨hab, hac⟩, hbc, fun h => h, List.nodup_nil⟩

/-- The sorting lemma: the alternating extension of the stored sorted-triple signs. -/
theorem xBit_eq {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ 8 D x) {a b c : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : xBit x a b c = D.neg3 a b c := by
  obtain ⟨w1, w2, -⟩ := hD
  have hab' : (a : Nat) ≠ b := fun h => hab (Fin.ext h)
  have hac' : (a : Nat) ≠ c := fun h => hac (Fin.ext h)
  have hbc' : (b : Nat) ≠ c := fun h => hbc (Fin.ext h)
  have T : ∀ p q r : Fin 8, (p : Nat) < q → (q : Nat) < r → x.testBit (triIdx p q r) = D.neg3 p q r :=
    fun p q r h1 h2 => hx.1 p q r h1 h2 r.isLt
  unfold xBit xT
  by_cases h1 : (a : Nat) < b
  · rw [if_pos h1]
    by_cases h2 : (b : Nat) < c
    · rw [if_pos h2]
      simp only [Bool.xor_false]
      exact T a b c h1 h2
    · rw [if_neg h2]
      by_cases h3 : (a : Nat) < c
      · rw [if_pos h3]
        simp only
        rw [T a c b h3 (by omega), w2 a b c (nodup3 hab hac hbc), Bool.xor_true, Bool.not_not]
      · rw [if_neg h3]
        simp only [Bool.xor_false]
        rw [T c a b (by omega) h1, w1 a c b (nodup3 hac hab hbc.symm),
          w2 a b c (nodup3 hab hac hbc), Bool.not_not]
  · rw [if_neg h1]
    by_cases h3 : (a : Nat) < c
    · rw [if_pos h3]
      simp only
      rw [T b a c (by omega) h3, w1 a b c (nodup3 hab hac hbc), Bool.xor_true, Bool.not_not]
    · rw [if_neg h3]
      by_cases h2 : (b : Nat) < c
      · rw [if_pos h2]
        simp only [Bool.xor_false]
        rw [T b c a h2 (by omega), w2 b a c (nodup3 hab.symm hbc hac),
          w1 a b c (nodup3 hab hac hbc), Bool.not_not]
      · rw [if_neg h2]
        simp only
        rw [T c b a (by omega) (by omega), w1 b c a (nodup3 hbc hab.symm hac.symm),
          w2 b a c (nodup3 hab.symm hbc hac), w1 a b c (nodup3 hab hac hbc), Bool.not_not,
          Bool.xor_true, Bool.not_not]

theorem eBit_eq {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ 8 D x) {a b : Fin 8}
    (hab : a ≠ b) : eBit x a b = D.neg2 a b := by
  have hab' : (a : Nat) ≠ b := fun h => hab (Fin.ext h)
  unfold eBit
  by_cases h : (a : Nat) < b
  · rw [if_pos h]; exact hx.2 a b h b.isLt
  · rw [if_neg h, hx.2 b a (by omega) a.isLt, hD.2.2 a b]

/-! ### The three kinds of instances -/

theorem gp_sound {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ 8 D x) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (h : ∀ q ∈ gpEqs a b c d e, q.eval x = false) : ¬ D.GPinst a b c d e := by
  simp only [gpEqs, List.forall_mem_cons] at h
  obtain ⟨h1, h2, -⟩ := h
  simp only [eval_add, eval_X, eval_one] at h1 h2
  rw [xBit_eq hD hx hab hac hbc, xBit_eq hD hx had hae hde, xBit_eq hD hx hab had hbd,
    xBit_eq hD hx hac hae hce] at h1
  rw [xBit_eq hD hx hab had hbd, xBit_eq hD hx hac hae hce, xBit_eq hD hx hab hae hbe,
    xBit_eq hD hx hac had hcd] at h2
  intro hG
  exact hG ⟨eq_of_xor_eq_false h1, eq_of_xor_eq_false h2⟩

/-- An equation with the constant xor-ed with `b`. -/
def tw (q : Eqn) (b : Bool) : Eqn := ⟨q.tog, q.c ^^ b⟩

theorem eval_tw (q : Eqn) (b : Bool) (x : Nat) : (tw q b).eval x = (q.eval x ^^ b) :=
  eval_mk_xor q b x

/-- The six circuit equations, explicitly. -/
theorem circEqs_eq (v0 v1 v2 v3 p : Nat) : circEqs v0 v1 v2 v3 p =
    [tw (Eqn.add (Eqn.add (Eqn.E v0 v1) (Eqn.X v1 v2 v3)) (Eqn.add Eqn.one (Eqn.X v0 v2 v3))) (p.testBit 0),
     tw (Eqn.add (Eqn.add (Eqn.E v0 v2) (Eqn.X v1 v2 v3)) (Eqn.X v0 v1 v3)) (p.testBit 1),
     tw (Eqn.add (Eqn.add (Eqn.E v0 v3) (Eqn.X v1 v2 v3)) (Eqn.add Eqn.one (Eqn.X v0 v1 v2))) (p.testBit 2),
     tw (Eqn.add (Eqn.add (Eqn.E v1 v2) (Eqn.add Eqn.one (Eqn.X v0 v2 v3))) (Eqn.X v0 v1 v3)) (p.testBit 3),
     tw (Eqn.add (Eqn.add (Eqn.E v1 v3) (Eqn.add Eqn.one (Eqn.X v0 v2 v3)))
       (Eqn.add Eqn.one (Eqn.X v0 v1 v2))) (p.testBit 4),
     tw (Eqn.add (Eqn.add (Eqn.E v2 v3) (Eqn.X v0 v1 v3)) (Eqn.add Eqn.one (Eqn.X v0 v1 v2))) (p.testBit 5)] :=
  rfl

/-- Boolean form of `SD.twoAt`. -/
def twoAtB (x y z c : Bool) : Bool := (x == c && y == c) || (x == c && z == c) || (y == c && z == c)

theorem twoAt_iff : ∀ x y z c : Bool, SD.twoAt x y z c ↔ twoAtB x y z c = true := by
  unfold SD.twoAt twoAtB
  decide

/-- For each of the 20 forbidden edge-flag patterns one colour class is a matching: some colour
is carried by at most one edge at every vertex. -/
theorem pat_spec : ∀ p < 64, (isMatching p false || isMatching p true) = true →
    ∃ c : Bool, (twoAtB (p.testBit 0) (p.testBit 1) (p.testBit 2) c ||
      twoAtB (p.testBit 0) (p.testBit 3) (p.testBit 4) c ||
      twoAtB (p.testBit 1) (p.testBit 3) (p.testBit 5) c ||
      twoAtB (p.testBit 2) (p.testBit 4) (p.testBit 5) c) = false := by
  decide +kernel

theorem circ_key {p : Nat} (hp : p < 64) (hpat : (isMatching p false || isMatching p true) = true)
    {s01 s02 s03 s12 s13 s23 : Bool} (h0 : s01 = p.testBit 0) (h1 : s02 = p.testBit 1)
    (h2 : s03 = p.testBit 2) (h3 : s12 = p.testBit 3) (h4 : s13 = p.testBit 4)
    (h5 : s23 = p.testBit 5)
    (hC : ∀ c : Bool, SD.twoAt s01 s02 s03 c ∨ SD.twoAt s01 s12 s13 c ∨ SD.twoAt s02 s12 s23 c ∨
      SD.twoAt s03 s13 s23 c) : False := by
  obtain ⟨c, hc⟩ := pat_spec p hp hpat
  subst h0 h1 h2 h3 h4 h5
  simp only [Bool.or_eq_false_iff] at hc
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
  rcases hC c with h | h | h | h <;> rw [twoAt_iff] at h
  · rw [hc1] at h; exact Bool.false_ne_true h
  · rw [hc2] at h; exact Bool.false_ne_true h
  · rw [hc3] at h; exact Bool.false_ne_true h
  · rw [hc4] at h; exact Bool.false_ne_true h

theorem circ_sound {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ 8 D x) {v0 v1 v2 v3 : Fin 8}
    {p : Nat} (hp : p < 64) (hpat : (isMatching p false || isMatching p true) = true)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (h : ∀ q ∈ circEqs v0 v1 v2 v3 p, q.eval x = false) : ¬ D.CircInst v0 v1 v2 v3 := by
  rw [circEqs_eq] at h
  simp only [List.forall_mem_cons] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := h
  simp only [eval_tw, eval_add, eval_X, eval_E, eval_one, Bool.true_xor,
    xBit_eq hD hx h12 h13 h23, xBit_eq hD hx h02 h03 h23, xBit_eq hD hx h01 h03 h13,
    xBit_eq hD hx h01 h02 h12, eBit_eq hD hx h01, eBit_eq hD hx h02, eBit_eq hD hx h03,
    eBit_eq hD hx h12, eBit_eq hD hx h13, eBit_eq hD hx h23] at e0 e1 e2 e3 e4 e5
  intro hC
  exact circ_key hp hpat (eq_of_xor_eq_false e0) (eq_of_xor_eq_false e1) (eq_of_xor_eq_false e2)
    (eq_of_xor_eq_false e3) (eq_of_xor_eq_false e4) (eq_of_xor_eq_false e5) hC

theorem forb_sound {D : SD} (hD : D.Wf) {x : Nat} (hx : AgreeJ 8 D x) {r s i j k : Fin 8}
    (hrs : r ≠ s) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (hsi : s ≠ i) (hsj : s ≠ j)
    (hsk : s ≠ k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∀ q ∈ forbEqs r s i j k, q.eval x = false) : ¬ D.ForbInst r s i j k := by
  simp only [forbEqs, List.forall_mem_cons] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  simp only [eval_add, eval_X, eval_E, eval_one,
    xBit_eq hD hx hrs hri hsi, xBit_eq hD hx hrs hrj hsj, xBit_eq hD hx hrs hrk hsk,
    xBit_eq hD hx hrj hrk hjk, xBit_eq hD hx hsj hsk hjk, xBit_eq hD hx hri hrj hij,
    xBit_eq hD hx hsi hsj hij, xBit_eq hD hx hri hrk hik, xBit_eq hD hx hsi hsk hik,
    eBit_eq hD hx hrs, eBit_eq hD hx hri, eBit_eq hD hx hrj, eBit_eq hD hx hrk,
    eBit_eq hD hx hsi, eBit_eq hD hx hsj, eBit_eq hD hx hsk, eBit_eq hD hx hij,
    eBit_eq hD hx hik] at h1 h2 h3 h4 h5 h6 h7
  intro hF
  exact hF ⟨eq_of_xor_eq_false h1, eq_of_xor_eq_false h2, eq_of_xor_eq_false h3,
    eq_of_xor_eq_false h4, eq_of_xor_eq_false h5, eq_of_xor_eq_false h6,
    eq_not_of_xor_xor_true h7⟩

/-! ### Well-formed instances -/

theorem wfB_labs {n : Nat} {inst : Inst} (hwf : inst.wfB n = true) :
    (∀ a ∈ inst.labs, a ≤ n) ∧ inst.labs.Nodup := by
  unfold Inst.wfB at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  exact ⟨hwf.1.1, hwf.1.2⟩

theorem wfB_circ {n v0 v1 v2 v3 p : Nat} (hwf : (Inst.circ v0 v1 v2 v3 p).wfB n = true) :
    (isMatching p false || isMatching p true) = true ∧ p < 64 := by
  unfold Inst.wfB at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  exact hwf.2

theorem fne {a b : Fin 8} (h : (a : Nat) ≠ b) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Corrected form of `Kc.Inst.sound`: with the additional hypothesis `n ≤ 7` (so that all labels
are `< 8` and `Fin.ofNat 8` is the identity on them). -/
theorem inst_sound (n : Nat) (hn : n ≤ 7) (D : SD) (hD : D.Wf) (x : Nat) (hx : AgreeJ 8 D x)
    (inst : Kc.Inst) (hwf : inst.wfB n = true) (h : ∀ q ∈ inst.eqns, q.eval x = false) :
    ¬ inst.Holds D := by
  obtain ⟨hle, hnd⟩ := wfB_labs hwf
  cases inst with
  | gp a b c d e =>
    have ha := hle a (by simp [Inst.labs])
    have hb := hle b (by simp [Inst.labs])
    have hc := hle c (by simp [Inst.labs])
    have hd := hle d (by simp [Inst.labs])
    have he := hle e (by simp [Inst.labs])
    obtain ⟨A, rfl⟩ : ∃ A : Fin 8, (A : Nat) = a := ⟨⟨a, by omega⟩, rfl⟩
    obtain ⟨B, rfl⟩ : ∃ B : Fin 8, (B : Nat) = b := ⟨⟨b, by omega⟩, rfl⟩
    obtain ⟨C, rfl⟩ : ∃ C : Fin 8, (C : Nat) = c := ⟨⟨c, by omega⟩, rfl⟩
    obtain ⟨Dd, rfl⟩ : ∃ Dd : Fin 8, (Dd : Nat) = d := ⟨⟨d, by omega⟩, rfl⟩
    obtain ⟨E, rfl⟩ : ∃ E : Fin 8, (E : Nat) = e := ⟨⟨e, by omega⟩, rfl⟩
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, -⟩ := hnd
    simp only [Inst.Holds, Fin.ofNat_val_eq_self]
    exact gp_sound hD hx (fne hab) (fne hac) (fne had) (fne hae) (fne hbc) (fne hbd) (fne hbe)
      (fne hcd) (fne hce) (fne hde) (fun q hq => h q (List.mem_append_left _ hq))
  | circ v0 v1 v2 v3 p =>
    obtain ⟨hpat, hp⟩ := wfB_circ hwf
    have h0 := hle v0 (by simp [Inst.labs])
    have h1 := hle v1 (by simp [Inst.labs])
    have h2 := hle v2 (by simp [Inst.labs])
    have h3 := hle v3 (by simp [Inst.labs])
    obtain ⟨V0, rfl⟩ : ∃ V : Fin 8, (V : Nat) = v0 := ⟨⟨v0, by omega⟩, rfl⟩
    obtain ⟨V1, rfl⟩ : ∃ V : Fin 8, (V : Nat) = v1 := ⟨⟨v1, by omega⟩, rfl⟩
    obtain ⟨V2, rfl⟩ : ∃ V : Fin 8, (V : Nat) = v2 := ⟨⟨v2, by omega⟩, rfl⟩
    obtain ⟨V3, rfl⟩ : ∃ V : Fin 8, (V : Nat) = v3 := ⟨⟨v3, by omega⟩, rfl⟩
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hnd
    simp only [Inst.Holds, Fin.ofNat_val_eq_self]
    exact circ_sound hD hx hp hpat (fne h01) (fne h02) (fne h03) (fne h12) (fne h13) (fne h23)
      (fun q hq => h q (List.mem_append_left _ hq))
  | forb r s i j k =>
    have hr := hle r (by simp [Inst.labs])
    have hs := hle s (by simp [Inst.labs])
    have hi := hle i (by simp [Inst.labs])
    have hj := hle j (by simp [Inst.labs])
    have hk := hle k (by simp [Inst.labs])
    obtain ⟨R, rfl⟩ : ∃ R : Fin 8, (R : Nat) = r := ⟨⟨r, by omega⟩, rfl⟩
    obtain ⟨S, rfl⟩ : ∃ S : Fin 8, (S : Nat) = s := ⟨⟨s, by omega⟩, rfl⟩
    obtain ⟨I, rfl⟩ : ∃ I : Fin 8, (I : Nat) = i := ⟨⟨i, by omega⟩, rfl⟩
    obtain ⟨J, rfl⟩ : ∃ J : Fin 8, (J : Nat) = j := ⟨⟨j, by omega⟩, rfl⟩
    obtain ⟨K, rfl⟩ : ∃ K : Fin 8, (K : Nat) = k := ⟨⟨k, by omega⟩, rfl⟩
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨hrs, hri, hrj, hrk⟩, ⟨hsi, hsj, hsk⟩, ⟨hij, hik⟩, hjk, -⟩ := hnd
    simp only [Inst.Holds, Fin.ofNat_val_eq_self]
    exact forb_sound hD hx (fne hrs) (fne hri) (fne hrj) (fne hrk) (fne hsi) (fne hsj) (fne hsk)
      (fne hij) (fne hik) (fne hjk) (fun q hq => h q (List.mem_append_left _ hq))

end KEqn

/-- If all equations of a well-formed instance are satisfied by `x`, where `x` agrees with a
well-formed `D`, then the instance is violated by `D`.  (The bound `n ≤ 7` keeps every label of the
instance inside `Fin 8`; without it the statement is false: labels `≥ 8` are not read by `AgreeJ 8`.) -/
theorem Kc.Inst.sound (n : Nat) (hn : n ≤ 7) (D : SD) (hD : D.Wf) (x : Nat) (hx : AgreeJ 8 D x)
    (inst : Kc.Inst) (hwf : inst.wfB n = true) (h : ∀ q ∈ inst.eqns, q.eval x = false) :
    ¬ inst.Holds D :=
  KEqn.inst_sound n hn D hD x hx inst hwf h

/-- Parity of the bits of `m &&& x` among the first `84` bit positions. -/
def parity84 (m x : Nat) : Bool :=
  (List.range 84).foldl (fun acc v => acc ^^ (Nat.testBit m v && Nat.testBit x v)) false

namespace KEqn

/-! ### Parity form of the evaluation -/

theorem parFold_xor (x m m' : Nat) (l : List Nat) (a b : Bool) :
    l.foldl (fun acc v => acc ^^ ((m ^^^ m').testBit v && x.testBit v)) (a ^^ b) =
      (l.foldl (fun acc v => acc ^^ (m.testBit v && x.testBit v)) a ^^
        l.foldl (fun acc v => acc ^^ (m'.testBit v && x.testBit v)) b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldl_cons]
    have hacc : ((a ^^ b) ^^ ((m ^^^ m').testBit v && x.testBit v)) =
        ((a ^^ (m.testBit v && x.testBit v)) ^^ (b ^^ (m'.testBit v && x.testBit v))) := by
      rw [Nat.testBit_xor]
      generalize m.testBit v = c
      generalize m'.testBit v = d
      generalize x.testBit v = e
      revert a b c d e; decide
    rw [hacc, ih]

theorem parFold_single (x i : Nat) (l : List Nat) (hl : l.Nodup) (a : Bool) :
    l.foldl (fun acc v => acc ^^ ((1 <<< i).testBit v && x.testBit v)) a =
      (a ^^ (decide (i ∈ l) && x.testBit i)) := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, decide_false, Bool.false_and, Bool.xor_false]
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldl_cons]
    rw [ih hl.2, Nat.one_shiftLeft]
    by_cases hv : i = v
    · subst hv
      rw [Nat.testBit_two_pow_self, decide_eq_false hl.1, decide_eq_true List.mem_cons_self]
      simp only [Bool.true_and, Bool.false_and, Bool.xor_false]
    · rw [Nat.testBit_two_pow_of_ne hv]
      have hmem : (i ∈ v :: l) ↔ i ∈ l := by
        rw [List.mem_cons]; exact ⟨fun h => h.resolve_left hv, Or.inr⟩
      simp only [Bool.false_and, Bool.xor_false, hmem]

theorem parity84_zero (x : Nat) : parity84 0 x = false := by
  unfold parity84
  generalize List.range 84 = l
  suffices H : ∀ a, l.foldl (fun acc v => acc ^^ (Nat.testBit 0 v && Nat.testBit x v)) a = a from H false
  induction l with
  | nil => intro a; rfl
  | cons v l ih =>
    intro a
    simp only [List.foldl_cons, Nat.zero_testBit, Bool.false_and, Bool.xor_false] at ih ⊢
    exact ih a

theorem parity84_xor_single (m x i : Nat) (hi : i < 84) :
    parity84 (m ^^^ (1 <<< i)) x = (parity84 m x ^^ x.testBit i) := by
  have H := parFold_xor x m (1 <<< i) (List.range 84) false false
  rw [Bool.xor_false, parFold_single x i _ List.nodup_range,
    decide_eq_true (List.mem_range.mpr hi), Bool.true_and, Bool.false_xor] at H
  exact H

theorem parity84_mask (x : Nat) (tog : List Nat) (htog : ∀ i ∈ tog, i < 84) (m : Nat) :
    parity84 (tog.foldl (fun m i => m ^^^ (1 <<< i)) m) x =
      (parity84 m x ^^ tog.foldl (fun acc i => acc ^^ x.testBit i) false) := by
  induction tog generalizing m with
  | nil => simp only [List.foldl_nil, Bool.xor_false]
  | cons i t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun j hj => htog j (List.mem_cons_of_mem _ hj)),
      parity84_xor_single m x i (htog i List.mem_cons_self),
      foldl_xor (fun i => x.testBit i) t (false ^^ x.testBit i), Bool.false_xor, Bool.xor_assoc]

end KEqn

/-- An equation with all toggles `< 84` evaluates to the parity of its mask against `x`, xor its constant. -/
theorem Kc.Eqn.eval_eq_parity (q : Kc.Eqn) (hq : ∀ i ∈ q.tog, i < 84) (x : Nat) :
    q.eval x = (parity84 q.mask x ^^ q.c) := by
  rw [KEqn.eval_def, Eqn.mask, KEqn.parity84_mask x q.tog hq 0, KEqn.parity84_zero, Bool.false_xor,
    Bool.xor_comm]

namespace KEqn

/-! ### Toggled variables -/

/-- All toggles of the equation are variables `< 84`. -/
def TogLt (q : Eqn) : Prop := ∀ i ∈ q.tog, i < 84

theorem togLt_add {p q : Eqn} (hp : TogLt p) (hq : TogLt q) : TogLt (Eqn.add p q) := by
  intro i hi
  simp only [Eqn.add, List.mem_append] at hi
  exact hi.elim (hp i) (hq i)

theorem togLt_one : TogLt Eqn.one := fun _ hi => absurd hi List.not_mem_nil

theorem togLt_zero : TogLt Eqn.zero := fun _ hi => absurd hi List.not_mem_nil

theorem togLt_tw {q : Eqn} (hq : TogLt q) (b : Bool) : TogLt (tw q b) := hq

theorem xT_lt : ∀ a b c : Fin 8, (xT a b c).1 < 84 := by decide +kernel

theorem vE_lt : ∀ a b : Fin 8, a ≠ b → (if (a : Nat) < b then vE a b else vE b a) < 84 := by decide +kernel

theorem togLt_X {a b c : Nat} (ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 7) : TogLt (Eqn.X a b c) := by
  intro i hi
  simp only [Eqn.X, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  exact xT_lt ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩

theorem togLt_E {a b : Nat} (ha : a ≤ 7) (hb : b ≤ 7) (hab : a ≠ b) : TogLt (Eqn.E a b) := by
  intro i hi
  simp only [Eqn.E, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  exact vE_lt ⟨a, by omega⟩ ⟨b, by omega⟩ (fun h => hab (congrArg Fin.val h))

theorem togLt_pad8 {l : List Eqn} (hl : ∀ q ∈ l, TogLt q) : ∀ q ∈ pad8 l, TogLt q := by
  intro q hq
  simp only [pad8, List.mem_append, List.mem_replicate] at hq
  rcases hq with hq | ⟨-, rfl⟩
  · exact hl q hq
  · exact togLt_zero

end KEqn

/-- The equations of a well-formed instance (labels `≤ n ≤ 7`) toggle only variables `< 84`. -/
theorem Kc.Inst.eqns_tog_lt (n : Nat) (hn : n ≤ 7) (inst : Kc.Inst) (hwf : inst.wfB n = true) :
    ∀ q ∈ inst.eqns, ∀ i ∈ q.tog, i < 84 := by
  obtain ⟨hle, hnd⟩ := KEqn.wfB_labs hwf
  cases inst with
  | gp a b c d e =>
    have ha := hle a (by simp [Inst.labs])
    have hb := hle b (by simp [Inst.labs])
    have hc := hle c (by simp [Inst.labs])
    have hd := hle d (by simp [Inst.labs])
    have he := hle e (by simp [Inst.labs])
    refine KEqn.togLt_pad8 ?_
    simp only [gpEqs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true]
    refine ⟨?_, ?_⟩ <;>
      repeat' (first | exact KEqn.togLt_one | apply KEqn.togLt_add | apply KEqn.togLt_X)
    all_goals omega
  | circ v0 v1 v2 v3 p =>
    have h0 := hle v0 (by simp [Inst.labs])
    have h1 := hle v1 (by simp [Inst.labs])
    have h2 := hle v2 (by simp [Inst.labs])
    have h3 := hle v3 (by simp [Inst.labs])
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hnd
    refine KEqn.togLt_pad8 ?_
    rw [KEqn.circEqs_eq]
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply KEqn.togLt_tw <;>
      repeat' (first | exact KEqn.togLt_one | apply KEqn.togLt_add | apply KEqn.togLt_X |
        apply KEqn.togLt_E)
    all_goals omega
  | forb r s i j k =>
    have hr := hle r (by simp [Inst.labs])
    have hs := hle s (by simp [Inst.labs])
    have hi := hle i (by simp [Inst.labs])
    have hj := hle j (by simp [Inst.labs])
    have hk := hle k (by simp [Inst.labs])
    simp only [Inst.labs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨hrs, hri, hrj, hrk⟩, ⟨hsi, hsj, hsk⟩, ⟨hij, hik⟩, hjk, -⟩ := hnd
    refine KEqn.togLt_pad8 ?_
    simp only [forbEqs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat' (first | exact KEqn.togLt_one | apply KEqn.togLt_add | apply KEqn.togLt_X |
        apply KEqn.togLt_E)
    all_goals omega

/-- Every instance has exactly eight equations. -/
theorem Kc.Inst.eqns_length (inst : Kc.Inst) : inst.eqns.length = 8 := by
  cases inst <;> rfl

namespace KEqn

theorem mask_testBit_ne (tog : List Nat) (m v : Nat) (hv : ∀ i ∈ tog, i ≠ v) :
    (tog.foldl (fun m i => m ^^^ (1 <<< i)) m).testBit v = m.testBit v := by
  induction tog generalizing m with
  | nil => rfl
  | cons i t ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => hv j (List.mem_cons_of_mem _ hj)), Nat.testBit_xor, Nat.one_shiftLeft,
      Nat.testBit_two_pow_of_ne (hv i List.mem_cons_self), Bool.xor_false]

end KEqn

/-- The code of an equation stores the mask in the low bits and the constant in bit `100`. -/
theorem Kc.Eqn.code_testBit_lt (q : Kc.Eqn) (hq : ∀ i ∈ q.tog, i < 84) (v : Nat) (hv : v < 100) :
    (Kc.Eqn.code q).testBit v = q.mask.testBit v := by
  obtain ⟨tog, c⟩ := q
  unfold Eqn.code
  rw [Nat.testBit_or]
  cases c
  · simp only [cond_false, Nat.zero_testBit, Bool.or_false]
  · simp only [cond_true, Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne (by omega : 100 ≠ v),
      Bool.or_false]

theorem Kc.Eqn.code_testBit_100 (q : Kc.Eqn) (hq : ∀ i ∈ q.tog, i < 84) :
    (Kc.Eqn.code q).testBit 100 = q.c := by
  obtain ⟨tog, c⟩ := q
  unfold Eqn.code Eqn.mask
  rw [Nat.testBit_or, KEqn.mask_testBit_ne tog 0 100 (fun i hi => by have := hq i hi; omega),
    Nat.zero_testBit, Bool.false_or]
  cases c
  · simp only [cond_false, Nat.zero_testBit]
  · simp only [cond_true, Nat.one_shiftLeft, Nat.testBit_two_pow_self]

namespace KEqn

theorem nodup_ofNat {l : List Nat} (hl : ∀ a ∈ l, a < 8) (hnd : l.Nodup) :
    (l.map (Fin.ofNat 8)).Nodup := by
  refine List.Nodup.map_on ?_ hnd
  intro a ha b hb hab
  have h := congrArg Fin.val hab
  simp only [Fin.val_ofNat] at h
  rwa [Nat.mod_eq_of_lt (hl a ha), Nat.mod_eq_of_lt (hl b hb)] at h

end KEqn

/-- A valid sign datum satisfies every well-formed instance (labels `≤ 7`). -/
theorem Kc.Inst.holds_of_valid (n : Nat) (hn : n ≤ 7) (inst : Kc.Inst) (hwf : inst.wfB n = true)
    (D : SD) (hD : D.Valid8) : inst.Holds D := by
  obtain ⟨-, hGP, hC, hF⟩ := hD
  obtain ⟨hle, hnd⟩ := KEqn.wfB_labs hwf
  have hnd' := KEqn.nodup_ofNat (fun a ha => by have := hle a ha; omega) hnd
  cases inst with
  | gp a b c d e => exact hGP _ _ _ _ _ hnd'
  | circ v0 v1 v2 v3 p => exact hC _ _ _ _ hnd'
  | forb r s i j k => exact hF _ _ _ _ _ hnd'

end Results.EightEquidistantLines
